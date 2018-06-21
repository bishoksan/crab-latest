
#pragma once
#include <iostream>
#include <crab/common/wrapint.hpp>
#include <crab/common/types.hpp>
#include <crab/common/stats.hpp>
#include <crab/domains/operators_api.hpp>

#include <crab/domains/intervals.hpp>
#include <crab/domains/wrapped_interval_domain.hpp>
#include <crab/domains/combined_domains.hpp>
#include <crab/domains/patricia_trees.hpp>


//for creating variables
#include <crab/cfg/var_factory.hpp>
using namespace crab::cfg_impl;

using namespace std;
namespace crab {
    namespace domains {

        // A wrapper for combining wrapped-interval domain with any numerical domain
        //for the analysis of fixed width integer manipulating programs

        template<typename Domain1, typename Domain2>
        class wrapped_numerical_domain_sk :
        public abstract_domain<typename Domain1::number_t, typename Domain1::varname_t,
        wrapped_numerical_domain_sk<Domain1, Domain2> > {
        public:

            typedef abstract_domain<typename Domain1::number_t, typename Domain1::varname_t,
            wrapped_numerical_domain_sk<Domain1, Domain2> > abstract_domain_t;

            using typename abstract_domain_t::linear_expression_t;
            using typename abstract_domain_t::linear_constraint_t;
            using typename abstract_domain_t::linear_constraint_system_t;
            using typename abstract_domain_t::variable_t;
            using typename abstract_domain_t::number_t;
            using typename abstract_domain_t::varname_t;
            using typename abstract_domain_t::variable_vector_t;

            typedef wrapint::bitwidth_t bitwidth_t;
            typedef patricia_tree_set< variable_t> variable_set_t;
            typedef bound<number_t> bound_t;


        private:

            typedef domain_product2<number_t, varname_t, Domain1, Domain2> domain_product2_t;

        public:

            typedef interval<number_t> interval_t;
            typedef wrapped_interval<number_t> wrapped_interval_t;
            typedef wrapped_numerical_domain_sk<Domain1, Domain2> wrapped_numerical_domain_t;

        private:
            domain_product2_t _product;

            wrapped_numerical_domain_sk(domain_product2_t product) : _product(product) {
            }

            typedef interval_domain<number_t, varname_t> interval_domain_t;

            template<typename Dom>
            class to_intervals {
                Dom m_inv;
            public:

                to_intervals(Dom &inv) : m_inv(inv) {
                }

                interval_domain_t operator()() {
                    interval_domain_t res;
                    res += m_inv.to_linear_constraint_system();
                    return res;
                }
            };

            variable_t create_fresh_wrapped_int_var(linear_expression_t lexpr) {
                //assuming that all the variables in the constraints has the same bit-width
                variable_set_t vars = lexpr.variables();
                variable_t var = *(vars.begin());
                variable_t var_new(var.name().get_var_factory().get(), var.get_type(), var.get_bitwidth());

                return var_new;
            }

            /**this fuction is created only for renaming purpose**/
            variable_t create_fresh_int_var(variable_t var) {
                variable_t var_new(var.name().get_var_factory().get(), var.get_type());

                return var_new;
            }

            // *********************utilities functions begin: TODO: move to a right place *********************************************

            /*due to the implementation of get_signed_min, it should return - (value) for
             correctness
             FIXME
             */
            int64_t get_signed_min(bitwidth_t bit) {

                return -(crab::wrapint::get_signed_min(bit).get_uint64_t());
            }

            uint64_t get_signed_max(bitwidth_t bit) {

                return crab::wrapint::get_signed_max(bit).get_uint64_t();
            }

            uint64_t get_unsigned_max(bitwidth_t bit) {

                return crab::wrapint::get_unsigned_max(bit).get_uint64_t();
            }

            uint64_t get_unsigned_min(bitwidth_t bit) {

                return crab::wrapint::get_unsigned_min(bit).get_uint64_t();
            }

            uint64_t get_modulo(bitwidth_t bit) {

                return crab::wrapint::get_mod(bit);
            }

            bool nr_within_bound(number_t nr, number_t min, number_t max) {

                return (nr >= min && nr <= max);
            }

            number_t wrap_num_2_fix_width(number_t nr, bitwidth_t bit, bool is_signed) {
                uint64_t modulo = get_modulo(bit);
                number_t res = nr % modulo;
                bool nr_in_range;
                if (is_signed) {
                    nr_in_range = nr_within_bound(res, get_signed_min(bit), get_signed_max(bit));
                } else {
                    nr_in_range = nr_within_bound(res, get_unsigned_min(bit), get_unsigned_max(bit));
                }

                if (nr_in_range) {
                    return res;
                }
                if (res < 0) {
                    //underflow
                    return number_t(res + modulo);
                }
                if (res > 0) {
                    //overflow

                    return number_t(res - modulo);
                }
                return res;
            }

            // *********************utilities functions end: TODO: move to a right place *********************************************

            linear_constraint_system_t get_var_bounds(const variable_t var, bool is_signed) {
                bitwidth_t bit = var.get_bitwidth();
                linear_constraint_system_t vars_bounds;
                if (is_signed) {
                    vars_bounds += (var >= number_t(get_signed_min(bit))); //creates MIN<=var
                    vars_bounds += (var <= number_t(get_signed_max(bit))); //creates var<=MAX
                } else {

                    vars_bounds += (var >= number_t(get_unsigned_min(bit))); //creates MIN<=var
                    vars_bounds += (var <= number_t(get_unsigned_max(bit))); //creates var<=MAX
                }

                return vars_bounds;
            }

            /*checks if there is an overflow before a branching condition, if so calls a wrapping operator.
             * csts: is a branching condition
             * pre: the second domain is non empty, csts is a single constraint
             * 
             * 
             * FIXME: given a constraint E <=n, the expr returns E-n and const returns n
             * 
             * TODO: now the constraints are in  E <=n form, it needs extension to E1<= E2, wrapping of constant on rhs
             */
            void wrap_cond_exprs(Domain2& second, linear_constraint_t branch_cond, bool is_signed) {
                if (second.is_bottom()) return;
                number_t rhs_const = branch_cond.constant();
                //Given x+y<=1, expr is x+y-1 and const is 1
                //the following is done to cope up with the normalisation of linear constraints
                linear_expression_t lhs_branch_cond = branch_cond.expression() + rhs_const;
                //wrap rhs const and get a new system of constraints
                bool is_variable_lhs = lhs_branch_cond.is_variable();
                if (is_variable_lhs) {
                    CRAB_WARN(lhs_branch_cond, " is var ");
                    CRAB_WARN(" before wrap ", second);
                    wrap_single_var_SK(*(lhs_branch_cond.get_variable()), second, is_signed);
                    CRAB_WARN(" after wrap ", second);
                } else {
                    CRAB_WARN(lhs_branch_cond, " is expr ");
                    CRAB_WARN(" before wrap ", second);
                    wrap_expr_SK(branch_cond, second, is_signed);
                    CRAB_WARN(" after wrap ", second);
                }
            }

            linear_constraint_t wrap_rhs_and_get_new_constr(linear_constraint_t branch_cond, bool is_signed) {
                number_t rhs_const = branch_cond.constant();
                linear_expression_t lhs_branch_cond = branch_cond.expression() + rhs_const;
                number_t wrapped_rhs_const = wrap_const(branch_cond, rhs_const, is_signed);
                if (rhs_const == wrapped_rhs_const) {
                    //no wrapping of constant was done
                    return branch_cond;
                }
                //form a new constraint system
                linear_expression_t new_lhs_branch_expr = lhs_branch_cond - wrapped_rhs_const;

                return linear_constraint_t(new_lhs_branch_expr, branch_cond.kind());
            }

            number_t wrap_const(linear_constraint_t branch_cond, number_t rhs_const, bool is_signed) {
                bitwidth_t bit = (*(branch_cond.variables().begin())).get_bitwidth();
                return wrap_num_2_fix_width(rhs_const, bit, is_signed);
            }

            /*wraps a branching condition, for now only the left cond
             */
            void wrap_expr_SK(linear_constraint_t branch_cond, Domain2& second, bool is_signed) {
                number_t rhs = branch_cond.constant();
                linear_expression_t lhs = branch_cond.expression() + rhs;
                //CRAB_WARN("expr ", lhs, " overflew");
                variable_set_t lhs_vars = lhs.variables();
                //wrap all vars
                for (auto var : lhs_vars) {
                    wrap_single_var_SK(var, second, is_signed);
                    //second -= var;
                }
                //wrap the expr
                variable_t var_new = create_fresh_wrapped_int_var(lhs);
                second += (lhs == var_new);
                wrap_single_var_SK(var_new, second, is_signed);
                second -= var_new;
            }

            /*Simon and Kings method of wrapping a single variable
             * the abstract domain that need to be wrapped is the numerical one (second)
             * threshold puts a limit on how many disjunctions to produce while wrapping
             * TODO: move this threshold parameter to the top call
             */

            void wrap_single_var_SK(variable_t var, Domain2& second, bool is_signed, int threshold = 16) {
                //CRAB_WARN("wrap_single_var_SK CALLED, second, var ", second, " ", var);
                bitwidth_t bit = var.get_bitwidth();
                uint64_t modulo = get_modulo(bit);
                int lower_quad_index, upper_quad_index;
                //TODO: pass as a parameter, move this code
                to_intervals<Domain2> inv2(second);
                auto i_domain = inv2();
                interval_t var_interval = i_domain[var];
                //CRAB_WARN("var-interval ", var, " -", var_interval);
                if (var_interval.lb().is_finite() && var_interval.ub().is_finite()) {
                    auto lb = *(var_interval.lb().number());
                    auto ub = *(var_interval.ub().number());
                    //compute the quadrants
                    lower_quad_index = (long(lb) - get_signed_min(bit)) / modulo;
                    upper_quad_index = (long(ub) - get_signed_min(bit)) / modulo;
                    //CRAB_WARN("lower index upper index ", lower_quad_index, " ", upper_quad_index);
                }
                linear_constraint_system_t vars_bounds = get_var_bounds(var, is_signed);
                //Domain2 tmp;
                //tmp += vars_bounds;

                if (!var_interval.lb().is_finite() || !var_interval.ub().is_finite() || (upper_quad_index - lower_quad_index) > threshold) {
                    second -= var;
                    //conjoining variable bounds
                    second += vars_bounds;
                    //second = second & tmp;
                } else {
                    Domain2 res = Domain2::bottom();
                    if ((upper_quad_index == 0) && (lower_quad_index == 0)) {
                        res = second;
                    } else {
                        //shift and join quadrants
                        for (int i = lower_quad_index; i <= upper_quad_index; i++) {
                            Domain2 numerical_domain = second;
                            //CRAB_WARN("numerical  domain before replacement ", numerical_domain);
                            numerical_domain = update_var_in_domain(numerical_domain, var, i, modulo);
                            //CRAB_WARN("after replacement ", numerical_domain);
                            numerical_domain += vars_bounds;
                            //numerical_domain = numerical_domain & tmp;
                            res |= numerical_domain; //join all the quadrants
                        }
                    }
                    //CRAB_WARN("wraped res", res);
                    second = res;
                }
            }

            /*update a variable var with an Expr in an abstract domain
              Given an abstract domain p, and a variable v
             * the update is carried out by the following operation
             * exists u. (Rename(p, v, u) meet v= Expr(u, quotient, modulo))
             */

            Domain2& update_var_in_domain(Domain2& numerical_domain, variable_t var, int quotient, number_t modulo) {
                //rename a vector of variables  to another set of vectors
                //renaming var within the given abstract element
                variable_vector_t frm_vars, to_vars;
                frm_vars.push_back(var);
                //create a fresh variable, no need for a wrap-int variable since we are operating on domain2
                variable_t var_new = create_fresh_int_var(var);
                to_vars.push_back(var_new);
                //CRAB_WARN("about to rename ", var, " to ", var_new, " domain ", numerical_domain);
                numerical_domain.rename(frm_vars, to_vars);
                //CRAB_WARN("after renaming   domain ", numerical_domain);
                //expression to update var with
                linear_expression_t modulo_expr(modulo);
                linear_expression_t rhs_expr = quotient * modulo_expr;
                rhs_expr = var_new - rhs_expr;
                linear_constraint_t t = (var == rhs_expr);
                //CRAB_WARN("exprssion to update with ", t);
                numerical_domain += (var == rhs_expr);
                //project out var_new
                numerical_domain -= var_new;
                return numerical_domain;
                //return project_single_var<Domain2>(var_new, numerical_domain);
            }


        public:

            static wrapped_numerical_domain_t top() {

                return wrapped_numerical_domain_t(domain_product2_t::top());
            }

            static wrapped_numerical_domain_t bottom() {

                return wrapped_numerical_domain_t(domain_product2_t::bottom());
            }

        public:

            wrapped_numerical_domain_sk() : _product() {
            }

            wrapped_numerical_domain_sk(const wrapped_numerical_domain_t & other) :
            _product(other._product) {
            }

            wrapped_numerical_domain_t& operator=(const wrapped_numerical_domain_t & other) {
                if (this != &other) {

                    this->_product = other._product;
                }
                return *this;
            }

            bool is_bottom() {

                return this->_product.is_bottom();
            }

            bool is_top() {

                return this->_product.is_top();
            }

            bool operator<=(wrapped_numerical_domain_t other) {

                return (this->_product <= other._product);
            }

            bool operator==(wrapped_numerical_domain_t other) {

                return (this->_product == other._product);
            }

            void operator|=(wrapped_numerical_domain_t other) {

                this->_product |= other._product;
            }

            wrapped_numerical_domain_t operator|(wrapped_numerical_domain_t other) {

                return wrapped_numerical_domain_t(this->_product | other._product);
            }

            wrapped_numerical_domain_t operator&(wrapped_numerical_domain_t other) {

                return wrapped_numerical_domain_t(this->_product & other._product);
            }

            wrapped_numerical_domain_t operator||(wrapped_numerical_domain_t other) {
                wrapped_numerical_domain_t res(this->_product || other._product);

                return res;
            }

            template<typename Thresholds >
            wrapped_numerical_domain_t widening_thresholds(wrapped_numerical_domain_t other,
                    const Thresholds & ts) {

                return wrapped_numerical_domain_t(this->_product.widening_thresholds(other._product, ts));
            }

            wrapped_numerical_domain_t operator&&(wrapped_numerical_domain_t other) {

                return wrapped_numerical_domain_t(this->_product && other._product);
            }

            void assign(variable_t x, linear_expression_t e) {

                this->_product.assign(x, e);

            }

            void apply(operation_t op, variable_t x, variable_t y, variable_t z) {
                if (op == OP_DIVISION) {
                    // signed division
                    safen(y, true);
                    safen(z, true);
                }
                this->_product.apply(op, x, y, z);

            }

            void apply(operation_t op, variable_t x, variable_t y, number_t k) {
                if (op == OP_DIVISION) {
                    // signed division
                    safen(y, true);
                }
                this->_product.apply(op, x, y, k);

            }

            void set(variable_t v, interval_t x) {

                this->_product.set(v, x);
            }

            interval_t operator[](variable_t v) {

                return this->_product.second()[v];
            }

            virtual void backward_assign(variable_t x, linear_expression_t e,
                    wrapped_numerical_domain_t invariant) {

                this->_product.backward_assign(x, e, invariant._product);

            }

            virtual void backward_apply(operation_t op,
                    variable_t x, variable_t y, number_t k,
                    wrapped_numerical_domain_t invariant) {

                this->_product.backward_apply(op, x, y, k, invariant._product);
            }

            virtual void backward_apply(operation_t op,
                    variable_t x, variable_t y, variable_t z,
                    wrapped_numerical_domain_t invariant) {

                this->_product.backward_apply(op, x, y, z, invariant._product);
            }

            /*assume that the call to this operator is only coming from an assume  statement (branch/conditional)*/
            void operator+=(linear_constraint_system_t csts) {
                //CRAB_WARN("adding cond ", csts);
                if (csts.is_false()) {
                    this->_product.second() += csts;
                    this->_product.first() += csts;
                    return;
                }
                //                if (csts.size() == 0) { //is true
                //                    return;
                //                }
                //contains a single element and is tautology, means true
                //                if (csts.size() == 1) {
                //                    linear_constraint_t lc = *(csts.begin());
                //                    if (lc.is_tautology()) {
                //                        return;
                //                    }
                //                }
                //CRAB_WARN("=========== Wrap begin  second =========== ", _product.second());
                for (auto cst : csts) {
                    if (!cst.is_tautology()) {
                        bool is_singed = is_signed_cmp(cst);
                        wrap_cond_exprs(this->_product.second(), cst, is_singed);
                        wrap_cond_exprs(this->_product.first(), cst, is_singed); //also apply to first because it will be the same domain
                    }
                }
                //CRAB_WARN("=========== Wrap end  second ===========", _product.second());
                //safe to add constraints
                this->_product.second() += csts;
                this->_product.first() += csts;

            }

            bool is_signed_cmp(const linear_constraint_t & cst) {
                bool is_singed = true; //default
                if (cst.is_inequality() || cst.is_strict_inequality()) {
                    is_singed = cst.is_signed() ? true : false;
                }
                return is_singed;
            }

            /** wraps a variable to its range, this is needed for all that does not commute with the modulo
              (branches, div, and rem).
             * */

            void safen(const variable_t& v, bool is_signed) {
                wrap_single_var_SK(v, _product.second(), is_signed);
                wrap_single_var_SK(v, _product.first(), is_signed);
            }

            void operator-=(variable_t v) {

                this->_product -= v;
            }

            // cast_operators_api

            void apply(int_conv_operation_t op, variable_t dst, variable_t src) {

                this->_product.apply(op, dst, src);

            }

            // bitwise_operators_api

            void apply(bitwise_operation_t op, variable_t x, variable_t y, variable_t z) {

                this->_product.apply(op, x, y, z);

            }

            void apply(bitwise_operation_t op, variable_t x, variable_t y, number_t k) {

                this->_product.apply(op, x, y, k);

            }

            // division_operators_api

            void apply(div_operation_t op, variable_t x, variable_t y, variable_t z) {
                safen(y, (op == OP_SDIV || op == OP_SREM) ? true : false);
                safen(z, (op == OP_SDIV || op == OP_SREM) ? true : false);
                if (op == OP_UDIV || op == OP_UREM) {
                    // if unsigned division then we only apply it on wrapped intervals
                    _product.first().apply(op, x, y, z);
                } else {
                    _product.apply(op, x, y, z);
                }
            }

            void apply(div_operation_t op, variable_t x, variable_t y, number_t k) {
                safen(y, (op == OP_SDIV || op == OP_SREM) ? true : false);
                if (op == OP_UDIV || op == OP_UREM) {
                    // if unsigned division then we only apply it on wrapped intervals
                    _product.first().apply(op, x, y, k);
                } else {
                    _product.apply(op, x, y, k);
                }

            }

            // array_operators_api

            virtual void array_assume(variable_t a,
                    linear_expression_t lb_idx,
                    linear_expression_t ub_idx,
                    linear_expression_t val) override {

                this->_product.array_assume(a, lb_idx, ub_idx, val);

            }

            virtual void array_load(variable_t lhs, variable_t a,
                    linear_expression_t i, ikos::z_number bytes) override {

                this->_product.array_load(lhs, a, i, bytes);
            }

            virtual void array_store(variable_t a,
                    linear_expression_t i,
                    linear_expression_t val,
                    ikos::z_number bytes,
                    bool is_singleton) override {

                this->_product.array_store(a, i, val, bytes, is_singleton);
            }

            virtual void array_assign(variable_t lhs, variable_t rhs) override {

                this->_product.array_assign(lhs, rhs);

            }
            // Ignored pointer_operators_api

            // boolean operators

            virtual void assign_bool_cst(variable_t lhs, linear_constraint_t rhs) override {

                this->_product.assign_bool_cst(lhs, rhs);

            }

            virtual void assign_bool_var(variable_t lhs, variable_t rhs,
                    bool is_not_rhs) override {

                this->_product.assign_bool_var(lhs, rhs, is_not_rhs);

            }

            virtual void apply_binary_bool(bool_operation_t op, variable_t x,
                    variable_t y, variable_t z) override {

                this->_product.apply_binary_bool(op, x, y, z);

            }

            virtual void assume_bool(variable_t v, bool is_negated) override {

                this->_product.assume_bool(v, is_negated);
            }

            // backward boolean operators

            virtual void backward_assign_bool_cst(variable_t lhs, linear_constraint_t rhs,
                    wrapped_numerical_domain_t inv) {

                this->_product.backward_assign_bool_cst(lhs, rhs, inv._product);

            }

            virtual void backward_assign_bool_var(variable_t lhs, variable_t rhs, bool is_not_rhs,
                    wrapped_numerical_domain_t inv) {

                this->_product.backward_assign_bool_var(lhs, rhs, is_not_rhs, inv._product);

            }

            virtual void backward_apply_binary_bool(bool_operation_t op,
                    variable_t x, variable_t y, variable_t z,
                    wrapped_numerical_domain_t inv) {

                this->_product.backward_apply_binary_bool(op, x, y, z, inv._product);

            }

            linear_constraint_system_t to_linear_constraint_system() {
                linear_constraint_system_t csts;
                csts += this->_product.to_linear_constraint_system();

                return csts;
            }

            virtual void rename(const variable_vector_t& from,
                    const variable_vector_t & to) override {

                this->_product.rename(from, to);

            }

            void write(crab::crab_os & o) {

                this->_product.write(o);
            }

            static std::string getDomainName() {

                return domain_product2_t::getDomainName();
            }

            // domain_traits_api

            void expand(variable_t x, variable_t new_x) {

                crab::domains::domain_traits<Domain1>::
                        expand(this->_product.first(), x, new_x);
                crab::domains::domain_traits<Domain2>::
                        expand(this->_product.second(), x, new_x);

            }

            void normalize() {

                crab::domains::domain_traits<Domain1>::
                        normalize(this->_product.first());
                crab::domains::domain_traits<Domain2>::
                        normalize(this->_product.second());
            }

            template <typename Range>
            void forget(Range vars) {

                crab::domains::domain_traits<Domain1>::
                        forget(this->_product.first(), vars.begin(), vars.end());
                crab::domains::domain_traits<Domain2>::
                        forget(this->_product.second(), vars.begin(), vars.end());

            }

            template <typename Range>
            void project(Range vars) {

                crab::domains::domain_traits<Domain1>::
                        project(this->_product.first(), vars.begin(), vars.end());
                crab::domains::domain_traits<Domain2>::
                        project(this->_product.second(), vars.begin(), vars.end());
            }
        }; // class wrapped_numerical_domain_sk

        template<typename Domain1, typename Domain2>
        class domain_traits <wrapped_numerical_domain_sk<Domain1, Domain2> > {
        public:

            typedef wrapped_numerical_domain_sk<Domain1, Domain2> wrapped_numerical_domain_t;
            typedef typename wrapped_numerical_domain_t::variable_t variable_t;

            template<class CFG>
            static void do_initialization(CFG cfg) {
            }

            static void normalize(wrapped_numerical_domain_t& inv) {

                inv.normalize();
            }

            static void expand(wrapped_numerical_domain_t& inv, variable_t x, variable_t new_x) {

                inv.expand(x, new_x);
            }

            template <typename Iter>
            static void forget(wrapped_numerical_domain_t& inv, Iter it, Iter end) {

                inv.forget(boost::make_iterator_range(it, end));
            }

            template <typename Iter>
            static void project(wrapped_numerical_domain_t& inv, Iter it, Iter end) {
                inv.project(boost::make_iterator_range(it, end));
            }
        };

    } // end namespace domains
} // namespace crab



