
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

            std::vector<interval_t> both_in_bound_math_ordered(number_t start, number_t end, bitwidth_t bit, bool is_signed) {
                std::vector<interval_t> res;
                bound_t lb(start);
                bound_t ub(end);
                if (in_same_hemisphere(start, end, bit, is_signed)) {
                    interval_t first(lb, ub);
                    res.push_back(first);
                    return res;
                }
                //else they are in the different hemisphere, this only happen in the signed case where the first is
                //in 1-hem and the second in 0-hem
                bound_t ub1(max_1_hemisphere(bit, is_signed));
                interval_t first_i(lb, ub1);
                bound_t lb2(min_0_hemisphere(bit, is_signed));
                interval_t second_i(lb2, ub);
                res.push_back(first_i);
                res.push_back(second_i);
                return res;

            }

            std::vector<interval_t> both_in_bound_math_unordered(number_t start, number_t end, bitwidth_t bit, bool is_signed) {
                bound_t lb(start);
                bound_t ub(end);
                std::vector<interval_t> res;

                bool start_hem = hemisphere_1(start, bit, is_signed);
                bool end_hem = hemisphere_1(end, bit, is_signed);

                //both in 0-hemisphere
                if (!start_hem && !end_hem) {
                    bound_t up1_both_0_hem(max_0_hemisphere(bit, is_signed));
                    interval_t first_both_0_hem(lb, up1_both_0_hem);

                    //bound_t up1_both_0_hem(max_0_hemisphere(bit, is_signed));
                    interval_t second_both_0_hem(bound_t(min_1_hemisphere(bit, is_signed)), bound_t(max_1_hemisphere(bit, is_signed)));

                    interval_t third_both_0_hem(bound_t(max_0_hemisphere(bit, is_signed)), ub);

                    res.push_back(first_both_0_hem);
                    res.push_back(second_both_0_hem);
                    res.push_back(third_both_0_hem);
                    return res;

                }

                //both in 1-hemisphere
                if (start_hem && end_hem) {
                    bound_t up1_both_1_hem(max_1_hemisphere(bit, is_signed));
                    interval_t first_both_1_hem(lb, up1_both_1_hem);

                    //bound_t up1_both_0_hem(max_0_hemisphere(bit, is_signed));
                    interval_t second_both_1_hem(bound_t(min_0_hemisphere(bit, is_signed)), bound_t(max_0_hemisphere(bit, is_signed)));

                    interval_t third_both_1_hem(bound_t(min_1_hemisphere(bit, is_signed)), ub);

                    res.push_back(first_both_1_hem);
                    res.push_back(second_both_1_hem);
                    res.push_back(third_both_1_hem);
                    return res;

                }

                //the first in 1 hemis and the second in 0 hemis, only possible for unsigned integer
                if (start_hem && !end_hem) {
                    bound_t up_1_0_hem(max_1_hemisphere(bit, is_signed));
                    interval_t first_1_0_hem(lb, up_1_0_hem);

                    //bound_t up1_both_0_hem(max_0_hemisphere(bit, is_signed));
                    interval_t second_1_0_hem(bound_t(min_0_hemisphere(bit, is_signed)), ub);


                    res.push_back(first_1_0_hem);
                    res.push_back(second_1_0_hem);
                    return res;
                }

                //the first in 0 hemis and the second in 1 hemis, only possible for signed integer
                if (!start_hem && end_hem) {
                    bound_t up_0_1_hem(max_0_hemisphere(bit, is_signed));
                    interval_t first_0_1_hem(lb, up_0_1_hem);

                    //bound_t up1_both_0_hem(max_0_hemisphere(bit, is_signed));
                    interval_t second_0_1_hem(bound_t(min_1_hemisphere(bit, is_signed)), ub);


                    res.push_back(first_0_1_hem);
                    res.push_back(second_0_1_hem);
                    return res;
                }
                return res;

            }

            /*given a wrap-interval for a variable, it produces its interpretation in mathematical interval (as array of intervals, which suppose to be joined)*/
            std::vector<interval_t> from_wrapped_to_intervals(variable_t v, wrapped_interval_t i, bool is_signed) {
                bitwidth_t bit = v.get_bitwidth();
                string start, end;
                if (is_signed) {
                    start = i.start().get_signed_str();
                    end = i.stop().get_signed_str();
                } else {
                    start = i.start().get_unsigned_str();
                    end = i.stop().get_unsigned_str();
                }
                //the following is needed since wrapped interval represents a sequence of bits
                number_t start_num = wrap_num_2_fix_width(number_t(start), bit, is_signed);
                number_t end_num = wrap_num_2_fix_width(number_t(end), bit, is_signed);

                std::vector<interval_t> res;

                //if both bounds are the same, the interval is singleton
                if (start_num == end_num) {
                    //both are in
                    interval_t first(start_num);
                    //return first;
                    res.push_back(start_num);
                    return res;
                }
                bool math_order = start_num <= end_num;
                if (math_order) {

                    return both_in_bound_math_ordered(start_num, end_num, bit, is_signed);
                }
                //else, not in  mathematical order
                return both_in_bound_math_unordered(start_num, end_num, bit, is_signed);
            }

            std::vector<linear_constraint_system_t> from_wrapped_interval_to_list_of_linear_constraints(variable_t v, wrapped_interval_t res, bool is_signed) {
                std::vector<interval_t> in = from_wrapped_to_intervals(v, res, is_signed);
                std::vector<linear_constraint_system_t> out;
                for (auto a : in) {
                    out.push_back(from_interval_to_linear_constraints(v, a));
                }
                return out;
            }

            linear_constraint_system_t from_interval_to_linear_constraints(variable_t v, interval_t res) {
                linear_constraint_system_t csts;
                if (!res.is_top()) {
                    boost::optional<number_t> lb = res.lb().number();
                    boost::optional<number_t> ub = res.ub().number();
                    if (lb) csts += linear_constraint_t(v >= *lb);
                    if (ub) csts += linear_constraint_t(v <= *ub);
                }
                return csts;
            }

            long long to_longl(std::string s) {

                return std::stoll(s, nullptr);
            }

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

            number_t min_0_hemisphere(bitwidth_t bit, bool is_signed) {

                return get_unsigned_min(bit); //0 for both signed and unsigned
            }

            number_t max_0_hemisphere(bitwidth_t bit, bool is_signed) {
                if (is_signed) {
                    return get_signed_max(bit);
                }
                return get_unsigned_max(bit);
            }

            number_t min_1_hemisphere(bitwidth_t bit, bool is_signed) {
                if (is_signed) {
                    return get_signed_min(bit);
                }
                return get_signed_max(bit) + 1;
            }

            number_t max_1_hemisphere(bitwidth_t bit, bool is_signed) {
                if (is_signed) {

                    return get_unsigned_min(bit) - 1;
                }
                return get_unsigned_max(bit);
            }

            /*
             returns true if the number is in  1-hemisphere
             */

            bool hemisphere_1(number_t res, bitwidth_t bit, bool is_signed) {
                return nr_within_bound(res, min_1_hemisphere(bit, is_signed), max_1_hemisphere(bit, is_signed));
            }

            bool in_same_hemisphere(number_t nr1, number_t nr2, bitwidth_t bit, bool is_signed) {
                bool nr1_hem = hemisphere_1(nr1, bit, is_signed);
                bool nr2_hem = hemisphere_1(nr2, bit, is_signed);

                return ((nr1_hem && nr2_hem) || (!nr1_hem && !nr2_hem));
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

            vector<linear_constraint_system_t> get_var_bounds_hemispherewise(const variable_t var, bool is_signed) {
                bitwidth_t bit = var.get_bitwidth();
                linear_constraint_system_t vars_bounds1, vars_bound2;
                vector<linear_constraint_system_t> bound_vec;
                if (is_signed) {
                    vars_bounds1 += (var >= number_t(min_1_hemisphere(bit, true)));
                    vars_bounds1 += (var <= number_t(max_1_hemisphere(bit, true)));
                    bound_vec.push_back(vars_bounds1);

                    vars_bound2 += (var >= number_t(min_0_hemisphere(bit, true)));
                    vars_bound2 += (var <= number_t(max_0_hemisphere(bit, true)));
                    bound_vec.push_back(vars_bound2);

                } else {

                    vars_bounds1 += (var >= number_t(min_1_hemisphere(bit, false)));
                    vars_bounds1 += (var <= number_t(max_1_hemisphere(bit, false)));
                    bound_vec.push_back(vars_bounds1);

                    vars_bound2 += (var >= number_t(min_0_hemisphere(bit, false)));
                    vars_bound2 += (var <= number_t(max_0_hemisphere(bit, false)));
                    bound_vec.push_back(vars_bound2);
                }

                return bound_vec;
            }

            /*always overflows for Simon and King*/
            bool expr_overflow(linear_expression_t lhs, const Domain1& first, bool is_signed) {
                return true;
            }

            /*return true if overflows, this is a generic method*/
            /*
             * 
               bool expr_overflow(linear_expression_t lhs, const Domain1& first, bool is_signed) {
                //should not modify first, take a copy
                Domain1 first_ref = first;
                variable_t var_new = create_fresh_wrapped_int_var(lhs);
                first_ref += (lhs == var_new);
                //return true; //expressions are always wrapped
                return var_overflow(var_new, first_ref, is_signed);
            }
            bool var_overflow(variable_t var, Domain1& first, bool is_signed) {
                if (first.is_bottom()) {
                    return false; //assume nothing will overflow
                }
                wrapped_interval_limit_value limit_val_domain = first.get_limit_value(var);
                if (limit_val_domain.is_bottom()) {
                    return false; //if bottom no overflow
                }
                if (limit_val_domain.is_top()) {
                    return true;
                }

                if (limit_val_domain.is_crossing_signed_limit() && is_signed) {
                    return true;
                }

                if (limit_val_domain.is_crossing_unsigned_limit() && !is_signed) {
                    return true;
                }
                return false;
            }
             */

            /*method tuned for Simon and King, it always overflows*/
            bool var_overflow(variable_t var, Domain1& first, bool is_signed) {
                if (first.is_bottom()) {
                    return false; //assume nothing will overflow
                }
                return false;
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
            void wrap_cond_exprs(Domain1& first, Domain2& second, linear_constraint_t branch_cond, bool is_signed) {
                if (second.is_bottom()) return;
                number_t rhs_const = branch_cond.constant();
                //Given x+y<=1, expr is x+y-1 and const is 1
                //the following is done to cope up with the normalisation of linear constraints
                linear_expression_t lhs_branch_cond = branch_cond.expression() + rhs_const;
                //wrap rhs const and get a new system of constraints
                linear_constraint_t new_lcs = wrap_rhs_and_get_new_constr(branch_cond, is_signed);
                bool is_variable_lhs = lhs_branch_cond.is_variable();
                bool is_const_lhs = lhs_branch_cond.is_constant();
                if (is_const_lhs) {
                    second += branch_cond;
                }
                if (is_variable_lhs) {
                    //CRAB_WARN(lhs_branch_cond, " is var ");
                    cond_wrap_var_SK(*(lhs_branch_cond.get_variable()), first, second, new_lcs, is_signed);
                } else {
                    //CRAB_WARN(lhs_branch_cond, " is expr ");
                    cond_wrap_expr_SK(new_lcs, first, second, is_signed);
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

            /*
             checks if a wrapping is necessary for this variable, if so,  do the necessary wrapping
             */
            void cond_wrap_var_SK(variable_t v, Domain1& first, Domain2& second, linear_constraint_t csts, bool is_signed) {
                if (var_overflow(v, first, is_signed)) {
                    //CRAB_WARN("var ", v, " overflew");
                    //call wrapping since it overflows
                    //wrap_a_var_based_on_wrapped_interval(v, first, second, csts, is_signed);
                    wrap_single_var_SK(v, second, csts, is_signed);
                } else {
                    //else it is safe to add constraints
                    second += csts;
                }
            }

            /*
             returns a vector of second domain elements, so that they are joined to the condition at the end to gain some precision
             */
            std::vector<Domain2> cond_wrap_exprs_var(variable_t v, Domain1& first, Domain2& second, bool is_signed) {
                std::vector<Domain2> dom2_elem;
                if (var_overflow(v, first, is_signed)) {
                    //CRAB_WARN("var ", v, " overflew: cond_wrap_exprs_var");
                    //call wrapping since it overflows
                    dom2_elem = wrap_var_SK_wo_adding_constrs(v, second, is_signed);
                } else {
                    dom2_elem.push_back(second);
                }
                return dom2_elem;
            }

            std::vector<Domain2> wrap_exprs_single_var(variable_t v, Domain1& first, vector<Domain2>& second_list, bool is_signed) {
                std::vector<Domain2> dom2_elem;
                for (Domain2 second : second_list) {
                    std::vector<Domain2> temp = cond_wrap_exprs_var(v, first, second, is_signed);
                    dom2_elem = append_vector<Domain2>(dom2_elem, temp);
                }
                return dom2_elem;
            }

            vector<variable_t> from_var_set_t_2_vector(variable_set_t vars) {
                vector<variable_t> var_vector;
                for (auto var : vars) {
                    var_vector.push_back(var);
                }
                return var_vector;
            }

            std::vector<Domain2> wrap_exprs_vars(vector<variable_t> var_vector, Domain1 & first, vector<Domain2> second_list, bool is_signed) {
                if (var_vector.empty()) {
                    return second_list;
                }
                boost::optional<variable_t> head_var = head_vector<variable_t>(var_vector);
                if (head_var) {
                    vector<Domain2> res_first_wrap = wrap_exprs_single_var(*head_var, first, second_list, is_signed);
                    return wrap_exprs_vars(tail_vector<variable_t>(var_vector), first, res_first_wrap, is_signed);
                }
                return second_list;
            }

            template <typename T>
            std::vector<T> append_vector(vector<T> a, vector<T> b) {
                if (a.empty()) {
                    return b;
                }
                a.insert(a.end(), b.begin(), b.end());

                return a;
            }

            template <typename T>
            std::vector<T> tail_vector(vector<T> a) {

                return std::vector<T>(a.begin() + 1, a.end());
            }

            template <typename T>
            boost::optional<T> head_vector(vector<T> a) {
                if (a.size() > 0)
                    return *(a.begin());

                return boost::optional<T>{};
            }

            /*wraps a branching condition if necessary, for now only the left cond
             if the expression does overflow, then wrap the expression by assigning it to a var; 
             * otherwise no wrapping is needed
             */
            void cond_wrap_expr_SK(linear_constraint_t branch_cond, Domain1& first, Domain2& second, bool is_signed) {
                number_t rhs = branch_cond.constant();
                linear_expression_t lhs = branch_cond.expression() + rhs;

                if (expr_overflow(lhs, first, is_signed)) {
                    //CRAB_WARN("expr ", lhs, " overflew");
                    variable_set_t lhs_vars = lhs.variables();
                    vector<Domain2> second_list;
                    second_list.push_back(second);
                    //It is enough to wrap the whole expr, no need to wrap the ind. variables in it
                    vector<Domain2> res_vars_wrap = wrap_exprs_vars(from_var_set_t_2_vector(lhs_vars), first, second_list, is_signed);
                    /**assuming well formed expressions, that is, all vars have the same bit-width in an expr
                     * */
                    variable_t var_new = create_fresh_wrapped_int_var(lhs);
                    res_vars_wrap = add_constrs_2_domains<Domain2>(res_vars_wrap, (lhs == var_new));
                    //TODO: do a switch on kind of constraint and form var_new KIND constant
                    linear_expression_t new_lhs_branch_expr = var_new - rhs;
                    //FIXME:  do a case split on kind and produce a right expr
                    linear_constraint_t new_cond = linear_constraint_t(new_lhs_branch_expr, branch_cond.kind());
                    second = wrap_var_in_all_domains<Domain2>(var_new, res_vars_wrap, new_cond, is_signed);
                    std::vector<variable_t> artifical_vars;
                    artifical_vars.push_back(var_new);
                    crab::domains::domain_traits<Domain2>::forget(second,
                            artifical_vars.begin(), artifical_vars.end());
                } else {
                    //else expression did not overflow. So it is safe to add constraints
                    second += branch_cond;
                }
            }

            template <typename T>
            T wrap_var_in_all_domains(variable_t v, vector<T> domains_2, linear_constraint_t new_cond, bool is_signed) {
                T res = T::bottom();
                for (auto dom2 : domains_2) {
                    wrap_single_var_SK(v, dom2, new_cond, is_signed);
                    res |= dom2;
                }
                return res;
            }

            template <typename T>
            vector<T> add_constrs_2_domains(vector<T> domains, linear_constraint_t lc) {
                vector<T> res;
                for (auto dom : domains) {
                    dom += lc;
                    res.push_back(dom);
                }
                return res;

            }

            void wrap_a_var_based_on_wrapped_interval(variable_t var, Domain1& first, Domain2& second, linear_constraint_t csts, bool is_signed) {
                second = project_single_var<Domain2>(var, second);
                wrapped_interval_t i_var = first[var];
                Domain2 second_cp = second; //copy of the second domain
                Domain2 acc = Domain2::bottom();
                if (!i_var.is_top()) {
                    std::vector<linear_constraint_system_t> lcss = from_wrapped_interval_to_list_of_linear_constraints(var, i_var, is_signed);
                    //TODO: improve this code
                    bool first_entry = true;
                    for (auto lcs : lcss) {
                        Domain2 temp = second_cp;
                        temp += lcs;
                        temp += csts;
                        if (first_entry) {
                            acc = temp;
                            first_entry = false;
                        } else {
                            acc |= temp; //join with the second
                        }
                    }
                    second = acc;
                } else {
                    //if it is  top, we can do [0, pos max] join [-neg min, neg max]
                    vector<linear_constraint_system_t> bounds = get_var_bounds_hemispherewise(var, is_signed);
                    Domain2 second_cp = second;

                    second += bounds.front();
                    second += csts;

                    second_cp += bounds.back();
                    second_cp += csts;

                    second |= second_cp;
                }
            }

            std::vector<Domain2> wrap_var_SK_wo_adding_constrs(variable_t var, Domain2& second, bool is_signed, int threshold = 16) {
                std::vector<Domain2> dom2_elem;
                second = project_single_var<Domain2>(var, second);

                bitwidth_t bit = var.get_bitwidth();
                uint64_t modulo = get_modulo(bit);
                int lower_quad_index, upper_quad_index;
                //TODO: pass as a parameter, move this code
                to_intervals<Domain2> inv2(second);
                auto i_domain = inv2();
                interval_t var_interval = i_domain[var];
                if (var_interval.lb().is_finite() && var_interval.ub().is_finite()) {
                    auto lb = *(var_interval.lb().number());
                    auto ub = *(var_interval.ub().number());
                    //compute the quadrants
                    lower_quad_index = (long(lb) - get_signed_min(bit)) / modulo;
                    upper_quad_index = (long(ub) - get_signed_min(bit)) / modulo;
                }
                linear_constraint_system_t vars_bounds = get_var_bounds(var, is_signed);

                if (!var_interval.lb().is_finite() || !var_interval.ub().is_finite() || (upper_quad_index - lower_quad_index) > threshold) {
                    project_single_var<Domain2>(var, second);
                    //conjoining variable bounds
                    second += vars_bounds;
                    dom2_elem.push_back(second);
                } else {
                    Domain2 res;
                    //shift and join quadrants
                    for (int i = lower_quad_index; i <= upper_quad_index; i++) {
                        Domain2 numerical_domain = second;
                        numerical_domain = update_var_in_domain(numerical_domain, var, i, modulo);
                        //meet,  
                        numerical_domain += vars_bounds;
                        res |= numerical_domain; //join all the quadrants
                    }
                    second = res;
                    // this->_product.second() = second;

                    dom2_elem.push_back(second);
                }
                return dom2_elem;
            }

            /*Simon and Kings method of wrapping a single variable
             consider the type of variable is signed, and the default bit is 32
             * the abstract domain that need to be wrapped is the numerical one (second)
             * threshold puts a limit on how many disjunctions to produce while wrapping
             * TODO: move this threshold parameter to the top call
             */

            void wrap_single_var_SK(variable_t var, Domain2& second, linear_constraint_system_t csts, bool is_signed, int threshold = 16) {
                //CRAB_WARN("wrap_single_var_SK CALLED, second ", second);
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

                if (!var_interval.lb().is_finite() || !var_interval.ub().is_finite() || (upper_quad_index - lower_quad_index) > threshold) {
                    //CRAB_WARN("one of the finiteness failed");
                    //project out var from the second domain and add variables bounds
                    //CRAB_WARN("second before proj ", second);
                    project_single_var<Domain2>(var, second);
                    //CRAB_WARN("second after proj ", second);

                    //conjoining variable bounds
                    second += vars_bounds;
                    return;
                } else {
                    Domain2 res;
                    //shift and join quadrants
                    for (int i = lower_quad_index; i <= upper_quad_index; i++) {
                        Domain2 numerical_domain = second;
                        //CRAB_WARN("numerical  domain before replacement ", numerical_domain);
                        numerical_domain = update_var_in_domain(numerical_domain, var, i, modulo);
                        //CRAB_WARN("after replacement ", numerical_domain);
                        //meet,  
                        numerical_domain += vars_bounds;
                        numerical_domain += csts;
                        res |= numerical_domain; //join all the quadrants
                    }
                    second = res;
                    //CRAB_WARN("resulting wrap domain ", second);
                    // this->_product.second() = second;

                    return;
                }
            }

            /*project out a variable var from a numerical abstract domain element second*/
            template <typename T>
            T & project_single_var(variable_t var, T & dom) {
                //TODO: improve it, not a right way to do
                std::vector<variable_t> vars;
                vars.push_back(var);
                crab::domains::domain_traits<T>::forget(dom,
                        vars.begin(), vars.end());

                return dom;
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
                return project_single_var<Domain2>(var_new, numerical_domain);
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
                //bool is_singed = signed_world();
                if (csts.is_false()) {
                    this->_product.second() += csts;
                    this->_product.first() += csts;
                    return;
                }
                if (csts.size() == 0) { //is true
                    return;
                }
                //contains a single element and is tautology, means true
                if (csts.size() == 1) {
                    linear_constraint_t lc = *(csts.begin());
                    if (lc.is_tautology()) {
                        return;
                    }
                }
                for (auto cst : csts) {
                    //ignore unsigned comparisons from the unsound domain
                    if (!(cst.is_inequality() && cst.is_unsigned())) {
                        bool is_singed = is_signed_cmp(cst);
                        wrap_cond_exprs(this->_product.first(), this->_product.second(), cst, is_singed); //makes second domain sound wrt modular arithmetic, so the following operation is sound
                    }
                }
                this->_product.first() += csts;
            }

            bool is_signed_cmp(const linear_constraint_t & cst) {
                bool is_singed = true; //default
                if (cst.is_inequality() || cst.is_strict_inequality()) {
                    is_singed = cst.is_signed() ? true : false;
                }
                return is_singed;
            }

            /** Basically forgets variable v from the unsound domain 
             * if the wrapped interval cannot deduce non-overflow 
             This is only applied to those operations that does not commute with the modulo
              (branches, div, and rem).
             * */

            void safen(const variable_t& v, bool is_signed) {
                if (var_overflow(v, _product.first(), is_signed)) {
                    _product.second() -= v;
                }
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



