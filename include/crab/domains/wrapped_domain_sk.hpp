/*******************************************************************************
 *
 * Implementation of Simon and King's method described in the paper:
 * Taming the wrapping of integer arithmetic (SAS'07).
 * Takes an arbritrary numerical abstract domain sound wrt mathematical integers
 * and makes it sound wrt machine arithmetic
 ******************************************************************************/
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

        // A wrapper for wrapped numerical domain

        template <typename NumDom, std::size_t max_reduction_cycles = 10 >
        class wrapped_domain_sk :
        public abstract_domain<typename NumDom::number_t,
        typename NumDom::varname_t, wrapped_domain_sk<NumDom> > {
        private:
            typedef typename NumDom::number_t N;
            typedef typename NumDom::varname_t V;
            typedef wrapped_domain_sk<NumDom> wrapped_numerical_domain_t;
            typedef abstract_domain<N, V, wrapped_numerical_domain_t> abstract_domain_t;

        public:
            using typename abstract_domain_t::linear_expression_t;
            using typename abstract_domain_t::linear_constraint_t;
            using typename abstract_domain_t::linear_constraint_system_t;
            using typename abstract_domain_t::variable_t;
            using typename abstract_domain_t::variable_vector_t;
            typedef typename linear_constraint_system_t::variable_set_t variable_set_t;
            typedef typename NumDom::number_t number_t;
            typedef typename NumDom::varname_t varname_t;
            typedef interval<N> interval_t;
            typedef crab::pointer_constraint<variable_t> ptr_cst_t;
            typedef typename variable_t::bitwidth_t bitwidth_t;
            typedef bound<number_t> bound_t;

        private:
            NumDom abs_num_dom;
        public:

            wrapped_domain_sk(const NumDom& dom) : abs_num_dom(dom) {
            }

            //the newly created variable will have the same bit-width of var

            variable_t create_fresh_wrapped_int_var(variable_t var) {
                variable_t var_new(var.name().get_var_factory().get(), var.get_type(), var.get_bitwidth());
                return var_new;
            }

            //this function is created only for renaming purpose

            variable_t create_fresh_int_var(variable_t var) {
                variable_t var_new(var.name().get_var_factory().get(), var.get_type());
                return var_new;
            }

            /*
             FIXME: strange that signed 32 and 64 bits min and max are the same
             */

            number_t get_signed_min(bitwidth_t bit) {
                number_t signed_min = crab::wrapint::get_signed_min(bit).get_signed_bignum();
                return signed_min;
            }

            number_t get_signed_max(bitwidth_t bit) {
                number_t signed_max = crab::wrapint::get_signed_max(bit).get_signed_bignum();
                return signed_max;
            }

            number_t get_unsigned_max(bitwidth_t bit) {
                number_t unsigned_max = crab::wrapint::get_unsigned_max(bit).get_unsigned_bignum();
                return unsigned_max;
            }

            number_t get_unsigned_min(bitwidth_t bit) {
                number_t unsigned_min = crab::wrapint::get_unsigned_min(bit).get_unsigned_bignum();
                return unsigned_min;
            }

            uint64_t get_modulo(bitwidth_t bit) {
                return crab::wrapint::get_mod(bit);
            }

            //returns bounding constraitns of a fixed width variable

            linear_constraint_system_t get_var_bounds(const variable_t var, bool is_signed) {
                bitwidth_t bit = var.get_bitwidth();
                linear_constraint_system_t vars_bounds;
                if (is_signed) {
                    vars_bounds += (var >= get_signed_min(bit)); //creates MIN<=var
                    vars_bounds += (var <= get_signed_max(bit)); //creates var<=MAX
                } else {

                    vars_bounds += (var >= get_unsigned_min(bit)); //creates MIN<=var
                    vars_bounds += (var <= get_unsigned_max(bit)); //creates var<=MAX
                }
                return vars_bounds;
            }

            /* wraps variables and exprs of branch_cond in abs_num_dom to their correct ranges
             * FIXME: given a constraint E <=n, the expr returns E-n and const returns n
             * 
             * TODO: now the constraints are in  E <=n form, it needs extension to E1<= E2
             */
            void wrap_cond_exprs(linear_constraint_t branch_cond, bool is_signed) {
                if (this->abs_num_dom.is_bottom()) return;
                number_t rhs_const = branch_cond.constant();
                //Given x+y<=1, expr is x+y-1 and const is 1
                //the following is done to cope up with the normalisation of linear constraints in crab
                linear_expression_t lhs_branch_cond = branch_cond.expression() + rhs_const;
                bool is_variable_lhs = lhs_branch_cond.is_variable();
                if (is_variable_lhs) {
                    wrap_single_var_SK(*(lhs_branch_cond.get_variable()), is_signed);
                } else {
                    wrap_expr_SK(branch_cond, is_signed);
                }
            }

            // wraps vars and exprs of branch_cond in abs_num_dom (enough to wrap the lhs due to crab normalisation)

            void wrap_expr_SK(linear_constraint_t branch_cond, bool is_signed) {
                number_t rhs = branch_cond.constant();
                linear_expression_t lhs = branch_cond.expression() + rhs;
                const variable_set_t &lhs_vars = lhs.variables();
                //wrap all vars before wrapping the expr
                for (auto var : lhs_vars) {
                    wrap_single_var_SK(var, is_signed);
                }
                //wrap the expr
                variable_t var_new = create_fresh_wrapped_int_var(*(lhs_vars.begin()));
                this->abs_num_dom += (lhs == var_new);
                wrap_single_var_SK(var_new, is_signed);
                this->abs_num_dom -= var_new;
            }

            /*Simon and Kings method of wrapping a single variable in a given numerical domain
             * threshold puts a limit on how many disjunctions to produce while wrapping
             * TODO: move this threshold parameter to the top or provide as const
             */

            void wrap_single_var_SK(variable_t var, bool is_signed, int threshold = 16) {
                //CRAB_WARN("wrap_single_var_SK CALLED, second ", second);
                bitwidth_t bit = var.get_bitwidth();
                uint64_t modulo = get_modulo(bit);
                int lower_quad_index, upper_quad_index;
                interval_t var_interval = abs_num_dom[var];
                //CRAB_WARN("var-interval ", var, " -", var_interval);
                if (var_interval.lb().is_finite() && var_interval.ub().is_finite()) {
                    auto lb = *(var_interval.lb().number());
                    auto ub = *(var_interval.ub().number());
                    //compute  quadrant's indices
                    lower_quad_index = (int) ((lb - get_signed_min(bit)) / modulo);
                    upper_quad_index = (int) ((ub - get_signed_min(bit)) / modulo);
                    //CRAB_WARN("lower index upper index ", lower_quad_index, " ", upper_quad_index);
                }
                linear_constraint_system_t vars_bounds = get_var_bounds(var, is_signed);

                if (!var_interval.lb().is_finite() || !var_interval.ub().is_finite() || (upper_quad_index - lower_quad_index) > threshold) {
                    this->abs_num_dom -= var;
                    //set to full range 
                    this->abs_num_dom += vars_bounds;
                } else {
                    //shift and join quadrants (induced by the indices)
                    if ((upper_quad_index == 0) && (lower_quad_index == 0)) {
                        //no shifting and joining is needed since shifting produces the same single domain 
                        return;
                    } else {
                        NumDom res = NumDom::bottom();
                        //shift and join quadrants
                        for (int i = lower_quad_index; i <= upper_quad_index; i++) {
                            NumDom numerical_domain = this->abs_num_dom;
                            if (i != 0) {
                                numerical_domain = update_var_in_domain(numerical_domain, var, i, modulo);
                            }
                            numerical_domain += vars_bounds;
                            res |= numerical_domain; //join all the quadrants
                        }
                        this->abs_num_dom = res;
                    }

                }
            }

            /*update a variable var with an Expr in an abstract domain
              Given an abstract domain p, and a variable v
             * the update is carried out by the following operation
             * exists u. (Rename(p, v, u) meet v= Expr(u, quotient, modulo))
             */

            NumDom& update_var_in_domain(NumDom& numerical_domain, variable_t var, int quotient, number_t modulo) {
                //rename a vector of variables  to another set of vectors
                //renaming var within the given abstract element
                variable_vector_t frm_vars, to_vars;
                frm_vars.push_back(var);
                //create a fresh variable, no need for a wrap-int variable since we are operating on a domain
                //that does not understand bounded vars
                variable_t var_new = create_fresh_int_var(var);
                to_vars.push_back(var_new);
                numerical_domain.rename(frm_vars, to_vars);
                //expression to update var with
                linear_expression_t modulo_expr(modulo);
                linear_expression_t rhs_expr = quotient * modulo_expr;
                rhs_expr = var_new - rhs_expr;
                numerical_domain += (var == rhs_expr);
                //project out var_new
                numerical_domain -= var_new;
                return numerical_domain;
            }


        public:

            static wrapped_numerical_domain_t top() {
                return wrapped_numerical_domain_t(NumDom::top());
            }

            static wrapped_numerical_domain_t bottom() {
                return wrapped_numerical_domain_t(NumDom::bottom());
            }

        public:

            wrapped_domain_sk() : abs_num_dom() {
            }

            wrapped_domain_sk(const wrapped_numerical_domain_t & other) : abs_num_dom(other.abs_num_dom) {
            }

            wrapped_numerical_domain_t& operator=(const wrapped_numerical_domain_t & other) {
                if (this != &other) {
                    this->abs_num_dom = other.abs_num_dom;
                }
                return *this;
            }

            bool is_bottom() {

                return this->abs_num_dom.is_bottom();
            }

            bool is_top() {

                return this->abs_num_dom.is_top();
            }

            bool operator<=(wrapped_numerical_domain_t other) {

                return (this->abs_num_dom <= other.abs_num_dom);
            }

            bool operator==(wrapped_numerical_domain_t other) {

                return (this->abs_num_dom == other.abs_num_dom);
            }

            void operator|=(wrapped_numerical_domain_t other) {

                this->abs_num_dom |= other.abs_num_dom;
            }

            wrapped_numerical_domain_t operator|(wrapped_numerical_domain_t other) {

                return wrapped_numerical_domain_t(this->abs_num_dom | other.abs_num_dom);
            }

            wrapped_numerical_domain_t operator&(wrapped_numerical_domain_t other) {

                return wrapped_numerical_domain_t(this->abs_num_dom & other.abs_num_dom);
            }

            wrapped_numerical_domain_t operator||(wrapped_numerical_domain_t other) {
                wrapped_numerical_domain_t res(this->abs_num_dom || other.abs_num_dom);

                return res;
            }

            template<typename Thresholds >
            wrapped_numerical_domain_t widening_thresholds(wrapped_numerical_domain_t other,
                    const Thresholds & ts) {

                return wrapped_numerical_domain_t(this->abs_num_dom.widening_thresholds(other.abs_num_dom, ts));
            }

            wrapped_numerical_domain_t operator&&(wrapped_numerical_domain_t other) {

                return wrapped_numerical_domain_t(this->abs_num_dom && other.abs_num_dom);
            }

            void assign(variable_t x, linear_expression_t e) {

                this->abs_num_dom.assign(x, e);

            }

            void apply(operation_t op, variable_t x, variable_t y, variable_t z) {
                if (op == OP_DIVISION) {
                    // signed division
                    safen(y, true);
                    safen(z, true);
                }
                this->abs_num_dom.apply(op, x, y, z);

            }

            void apply(operation_t op, variable_t x, variable_t y, number_t k) {
                if (op == OP_DIVISION) {
                    // signed division
                    safen(y, true);
                }
                this->abs_num_dom.apply(op, x, y, k);

            }

            void set(variable_t v, interval_t x) {

                this->abs_num_dom.set(v, x);
            }

            interval_t operator[](variable_t v) {

                return this->abs_num_dom[v];
            }

            virtual void backward_assign(variable_t x, linear_expression_t e,
                    wrapped_numerical_domain_t invariant) {

                this->abs_num_dom.backward_assign(x, e, invariant.abs_num_dom);

            }

            virtual void backward_apply(operation_t op,
                    variable_t x, variable_t y, number_t k,
                    wrapped_numerical_domain_t invariant) {

                this->abs_num_dom.backward_apply(op, x, y, k, invariant.abs_num_dom);
            }

            virtual void backward_apply(operation_t op,
                    variable_t x, variable_t y, variable_t z,
                    wrapped_numerical_domain_t invariant) {

                this->abs_num_dom.backward_apply(op, x, y, z, invariant.abs_num_dom);
            }

            /*assume that the call to this operator is only coming from an assume  statement (branch/conditional)*/
            void operator+=(linear_constraint_system_t csts) {
                if (csts.is_false()) {
                    this->abs_num_dom += csts;
                    return;
                }
                for (auto cst : csts) {
                    if (!cst.is_tautology()) {
                        bool is_singed = is_signed_cmp(cst);
                        wrap_cond_exprs(cst, is_singed);
                    }
                }
                //safe to add constraints since all vars and exprs of csts are set to their bounds
                this->abs_num_dom += csts;
            }

            //note that we assume the default is signed

            bool is_signed_cmp(const linear_constraint_t & cst) {
                bool is_singed = true; //default
                if (cst.is_inequality() || cst.is_strict_inequality()) {
                    is_singed = cst.is_signed() ? true : false;
                }
                return is_singed;
            }

            /* produces a wrapped value of a variable. This need to be called by all operations 
             that do not commute with the modulo (branches, div, and rem).
             */

            void safen(const variable_t& v, bool is_signed) {
                //abs_num_dom -=v; //this loses a lot of precision
                wrap_single_var_SK(v, is_signed);

            }

            void operator-=(variable_t v) {

                this->abs_num_dom -= v;
            }

            // cast_operators_api

            void apply(int_conv_operation_t op, variable_t dst, variable_t src) {

                this->abs_num_dom.apply(op, dst, src);

            }

            // bitwise_operators_api

            void apply(bitwise_operation_t op, variable_t x, variable_t y, variable_t z) {

                this->abs_num_dom.apply(op, x, y, z);

            }

            void apply(bitwise_operation_t op, variable_t x, variable_t y, number_t k) {

                this->abs_num_dom.apply(op, x, y, k);

            }

            // division_operators_api

            void apply(div_operation_t op, variable_t x, variable_t y, variable_t z) {
                safen(y, (op == OP_SDIV || op == OP_SREM) ? true : false);
                safen(z, (op == OP_SDIV || op == OP_SREM) ? true : false);
                if (op == OP_UDIV || op == OP_UREM) {
                    // if unsigned division then we only apply it on wrapped intervals
                    this->abs_num_dom.apply(op, x, y, z);
                } else {
                    this->abs_num_dom.apply(op, x, y, z);
                }
            }

            void apply(div_operation_t op, variable_t x, variable_t y, number_t k) {
                safen(y, (op == OP_SDIV || op == OP_SREM) ? true : false);
                if (op == OP_UDIV || op == OP_UREM) {
                    // if unsigned division then we only apply it on wrapped intervals
                    this->abs_num_dom.apply(op, x, y, k);
                } else {
                    this->abs_num_dom.apply(op, x, y, k);
                }

            }

            // array_operators_api

            virtual void array_assume(variable_t a,
                    linear_expression_t lb_idx,
                    linear_expression_t ub_idx,
                    linear_expression_t val) override {

                this->abs_num_dom.array_assume(a, lb_idx, ub_idx, val);

            }

            virtual void array_load(variable_t lhs, variable_t a,
                    linear_expression_t i, ikos::z_number bytes) override {

                this->abs_num_dom.array_load(lhs, a, i, bytes);
            }

            virtual void array_store(variable_t a,
                    linear_expression_t i,
                    linear_expression_t val,
                    ikos::z_number bytes,
                    bool is_singleton) override {

                this->abs_num_dom.array_store(a, i, val, bytes, is_singleton);
            }

            virtual void array_assign(variable_t lhs, variable_t rhs) override {

                this->abs_num_dom.array_assign(lhs, rhs);

            }
            // Ignored pointer_operators_api

            // boolean operators

            virtual void assign_bool_cst(variable_t lhs, linear_constraint_t rhs) override {

                this->abs_num_dom.assign_bool_cst(lhs, rhs);

            }

            virtual void assign_bool_var(variable_t lhs, variable_t rhs,
                    bool is_not_rhs) override {

                this->abs_num_dom.assign_bool_var(lhs, rhs, is_not_rhs);

            }

            virtual void apply_binary_bool(bool_operation_t op, variable_t x,
                    variable_t y, variable_t z) override {

                this->abs_num_dom.apply_binary_bool(op, x, y, z);

            }

            virtual void assume_bool(variable_t v, bool is_negated) override {

                this->abs_num_dom.assume_bool(v, is_negated);
            }

            // backward boolean operators

            virtual void backward_assign_bool_cst(variable_t lhs, linear_constraint_t rhs,
                    wrapped_numerical_domain_t inv) {

                this->abs_num_dom.backward_assign_bool_cst(lhs, rhs, inv.abs_num_dom);

            }

            virtual void backward_assign_bool_var(variable_t lhs, variable_t rhs, bool is_not_rhs,
                    wrapped_numerical_domain_t inv) {

                this->abs_num_dom.backward_assign_bool_var(lhs, rhs, is_not_rhs, inv.abs_num_dom);

            }

            virtual void backward_apply_binary_bool(bool_operation_t op,
                    variable_t x, variable_t y, variable_t z,
                    wrapped_numerical_domain_t inv) {

                this->abs_num_dom.backward_apply_binary_bool(op, x, y, z, inv.abs_num_dom);

            }

            linear_constraint_system_t to_linear_constraint_system() {
                linear_constraint_system_t csts;
                csts += this->abs_num_dom.to_linear_constraint_system();

                return csts;
            }

            virtual void rename(const variable_vector_t& from,
                    const variable_vector_t & to) override {

                this->abs_num_dom.rename(from, to);

            }

            void write(crab::crab_os & o) {

                this->abs_num_dom.write(o);
            }

            static std::string getDomainName() {

                return "SK-Wrapped" + NumDom::getDomainName();
            }

            // domain_traits_api

            void expand(variable_t x, variable_t new_x) {

                crab::domains::domain_traits<NumDom>::
                        expand(this->abs_num_dom, x, new_x);
            }

            void normalize() {

                crab::domains::domain_traits<NumDom>::
                        normalize(this->abs_num_dom);
            }

            template <typename Range>
            void forget(Range vars) {

                crab::domains::domain_traits<NumDom>::
                        forget(this->abs_num_dom, vars.begin(), vars.end());
            }

            template <typename Range>
            void project(Range vars) {

                crab::domains::domain_traits<NumDom>::
                        project(this->abs_num_dom, vars.begin(), vars.end());
            }
        }; // class wrapped_domain_sk

        template<typename NumD>
        class domain_traits <wrapped_domain_sk<NumD> > {
        public:

            typedef wrapped_domain_sk<NumD> wrapped_numerical_domain_t;
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



