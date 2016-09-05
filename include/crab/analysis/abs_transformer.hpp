#ifndef ABSTRACT_TRANSFORMER_HPP
#define ABSTRACT_TRANSFORMER_HPP

/* 
   Definition of abstract transfer functions.

   TODO: NumAbsTransformer should be extended with pointer operations
         so that we can have, for instance, reduced products of
         numerical domains with nullity.
 */

#include <boost/optional.hpp>
#include "boost/range/algorithm/set_algorithm.hpp"

#include <type_traits>

#include <crab/common/debug.hpp>
#include <crab/common/stats.hpp>
#include <crab/cfg/cfg.hpp>
#include <crab/domains/domain_traits.hpp>
#include <crab/domains/linear_constraints.hpp>

#include <crab/domains/nullity.hpp>

namespace crab {

  namespace analyzer {

  using namespace cfg;
  using namespace std;

  //! API abstract transformer
  template<typename VariableName>
  class abs_transformer_api: public statement_visitor <VariableName>
  {
   public:

    typedef VariableName varname_t;
    typedef variable < z_number, VariableName > z_var_t;
    typedef linear_expression< z_number, VariableName > z_lin_exp_t;
    typedef linear_constraint< z_number, VariableName > z_lin_cst_t;
    typedef linear_constraint_system< z_number, VariableName > z_lin_cst_sys_t;

    typedef binary_op <z_number,VariableName>        z_bin_op_t;
    typedef assignment <z_number,VariableName>       z_assign_t;
    typedef assume_stmt <z_number,VariableName>      z_assume_t;
    typedef havoc_stmt<VariableName>                 havoc_t;
    typedef unreachable_stmt<VariableName>           unreach_t;
    typedef select_stmt <z_number,VariableName>      z_select_t;
    typedef assert_stmt <z_number,VariableName>      z_assert_t;
    typedef callsite_stmt<VariableName>              callsite_t;
    typedef return_stmt<VariableName>                return_t;
    typedef array_init_stmt<VariableName>            z_arr_init_t;
    typedef assume_array_stmt<z_number,VariableName> z_assume_arr_t;
    typedef array_store_stmt<z_number,VariableName>  z_arr_store_t;
    typedef array_load_stmt<z_number,VariableName>   z_arr_load_t;
    typedef ptr_store_stmt<z_number,VariableName>    z_ptr_store_t;
    typedef ptr_load_stmt<z_number,VariableName>     z_ptr_load_t;
    typedef ptr_assign_stmt<z_number,VariableName>   z_ptr_assign_t;
    typedef ptr_object_stmt<VariableName>            ptr_object_t;
    typedef ptr_function_stmt<VariableName>          ptr_function_t;
    typedef ptr_null_stmt<VariableName>              ptr_null_t;
    typedef ptr_assume_stmt<VariableName>            ptr_assume_t;
    typedef ptr_assert_stmt<VariableName>            ptr_assert_t;

   protected: 

    virtual void exec (z_bin_op_t&)  { } 
    virtual void exec (z_assign_t&) { }
    virtual void exec (z_assume_t&) { }
    virtual void exec (havoc_t&) { }
    virtual void exec (unreach_t&) { }
    virtual void exec (z_select_t&) { }
    virtual void exec (z_assert_t&) { }
    virtual void exec (callsite_t&) { }
    virtual void exec (return_t&) { }
    virtual void exec (z_arr_init_t&) { }
    virtual void exec (z_assume_arr_t&) { }
    virtual void exec (z_arr_store_t&) { }
    virtual void exec (z_arr_load_t&) { }
    virtual void exec (z_ptr_store_t&) { }
    virtual void exec (z_ptr_load_t&) { }
    virtual void exec (z_ptr_assign_t&) { }
    virtual void exec (ptr_object_t&) { }
    virtual void exec (ptr_function_t&) { }
    virtual void exec (ptr_null_t&) { }
    virtual void exec (ptr_assume_t&) { }
    virtual void exec (ptr_assert_t&) { }

   public: /* visitor api */

    void visit (z_bin_op_t &s) { exec (s); }
    void visit (z_assign_t &s) { exec (s); }
    void visit (z_assume_t &s) { exec (s); }
    void visit (havoc_t &s) { exec (s); }
    void visit (unreach_t &s) { exec (s); }
    void visit (z_select_t &s) { exec (s); }
    void visit (z_assert_t &s) { exec (s); }
    void visit (callsite_t &s) { exec (s); }
    void visit (return_t &s) { exec (s); }
    void visit (z_arr_init_t &s) { exec (s); }
    void visit (z_assume_arr_t &s) { exec (s); }
    void visit (z_arr_store_t &s) { exec (s); }
    void visit (z_arr_load_t &s) { exec (s); }
    void visit (z_ptr_store_t &s) { exec (s); }
    void visit (z_ptr_load_t &s) { exec (s); }
    void visit (z_ptr_assign_t &s) { exec (s); }
    void visit (ptr_object_t &s) { exec (s); }
    void visit (ptr_function_t &s) { exec (s); }
    void visit (ptr_null_t &s) { exec (s); }
    void visit (ptr_assume_t &s) { exec (s); }
    void visit (ptr_assert_t &s) { exec (s); }

  };


  //! Abstract transformer specialized for numerical abstract domains
  //! with arrays but without pointers.
  template<typename NumAbsDomain, 
           typename SumTable /*unused*/, typename CallCtxTable /*unused*/>
  class num_abs_transformer: 
        public abs_transformer_api <typename CallCtxTable::abs_domain_t::varname_t>
  {

   public:

    typedef typename SumTable::abs_domain_t summ_abs_domain_t;
    typedef typename CallCtxTable::abs_domain_t call_abs_domain_t;
    typedef NumAbsDomain abs_dom_t;

   public:

    typedef abs_transformer_api <typename CallCtxTable::abs_domain_t::varname_t> abs_transform_t;
    using typename abs_transform_t::varname_t;
    using typename abs_transform_t::z_var_t;
    using typename abs_transform_t::z_lin_exp_t;
    using typename abs_transform_t::z_lin_cst_t;
    using typename abs_transform_t::z_lin_cst_sys_t;
    using typename abs_transform_t::z_bin_op_t;
    using typename abs_transform_t::z_assign_t;
    using typename abs_transform_t::z_assume_t;
    using typename abs_transform_t::z_select_t;
    using typename abs_transform_t::z_assert_t;
    using typename abs_transform_t::havoc_t;
    using typename abs_transform_t::unreach_t;
    using typename abs_transform_t::z_arr_init_t;
    using typename abs_transform_t::z_assume_arr_t;
    using typename abs_transform_t::z_arr_load_t;
    using typename abs_transform_t::z_arr_store_t;
    using typename abs_transform_t::callsite_t;

   protected:

    abs_dom_t& m_inv;

    template<typename T>
    void apply (abs_dom_t& inv, binary_operation_t op,
                varname_t x, varname_t y, T z) {

      auto op1 = conv_op<ikos::operation_t> (op);
      auto op2 = conv_op<ikos::div_operation_t> (op);
      auto op3 = conv_op<ikos::bitwise_operation_t> (op);
      
      if (op1) 
        inv.apply (*op1, x, y, z);
      else if (op2) 
        inv.apply (*op2, x, y, z);
      else if (op3)
        inv.apply (*op3, x, y, z);
      else
        CRAB_ERROR("unsupported binary operator", op);
    }
    
   public:

    num_abs_transformer (abs_dom_t& inv): 
        m_inv (inv) { }
    
    num_abs_transformer (abs_dom_t& inv, SumTable*, CallCtxTable*): 
        m_inv (inv) { }

    abs_dom_t& inv () { return m_inv; }

    void exec (z_bin_op_t& stmt)  {
      
      z_lin_exp_t op1 = stmt.left ();
      z_lin_exp_t op2 = stmt.right ();
      
      if (op1.get_variable () && op2.get_variable ())
      {
        apply (m_inv, stmt.op (), 
               stmt.lhs ().name(), 
               (*op1.get_variable ()).name(), 
               (*op2.get_variable ()).name());
      }
      else
      {
        assert ( op1.get_variable () && op2.is_constant ());
        apply (m_inv, stmt.op (), 
               stmt.lhs ().name (), 
               (*op1.get_variable ()).name(), 
               op2.constant ()); 
      }      
    }

    void exec (z_select_t& stmt) {
    
      abs_dom_t inv1 (m_inv);
      abs_dom_t inv2 (m_inv);
      inv1 += stmt.cond ();
      inv2 += stmt.cond ().negate ();
      if (inv2.is_bottom()) {
        inv1.assign (stmt.lhs().name (),stmt.left());
        m_inv = inv1;
      }
      else if (inv1.is_bottom ()) {
        inv2.assign (stmt.lhs().name (),stmt.right());
        m_inv = inv2;
      }
      else {
        inv1.assign (stmt.lhs().name (),stmt.left());
        inv2.assign (stmt.lhs().name (),stmt.right());
        m_inv = inv1 | inv2;
      }
    }    
    
    void exec (z_assign_t& stmt) {
      m_inv.assign (stmt.lhs().name (), z_lin_exp_t (stmt.rhs()));
    }
    
    void exec (z_assume_t& stmt) {
      m_inv += stmt.constraint();
    }

    void exec (havoc_t& stmt)  {
      m_inv -= stmt.variable();
    }

    void exec (unreach_t& stmt) {
      m_inv = abs_dom_t::bottom ();
    }

    void exec (z_assert_t& stmt) {
      abs_dom_t cst;
      cst += stmt.constraint();
      abs_dom_t meet = cst & m_inv;
      if (meet.is_bottom ()) {
        m_inv = abs_dom_t::bottom (); // assertion does not definitely hold.
        return;
      }
      m_inv += stmt.constraint ();
    }

    void exec (z_arr_init_t &stmt) {
      domains::array_domain_traits<abs_dom_t>::array_init (m_inv, 
                                                           stmt.variable (), 
                                                           stmt.values ());
    }

    void exec (z_assume_arr_t &stmt) {
      domains::array_domain_traits<abs_dom_t>::assume_array (m_inv, 
                                                             stmt.variable (), 
                                                             stmt.val ());
    }
    
    void exec (z_arr_store_t &stmt) {
      if (stmt.index ().get_variable ())
      {
        auto arr = stmt.array ().name ();
        auto idx = *(stmt.index ().get_variable ());
        domains::array_domain_traits<abs_dom_t>::array_store (m_inv, 
                                                              arr,
                                                              idx.name(), 
                                                              stmt.value (),
                                                              stmt.elem_size(),
                                                              stmt.is_singleton ());
      }
    }

    void exec (z_arr_load_t  &stmt) {
      if (stmt.index ().get_variable ())
      {
        auto idx = *(stmt.index ().get_variable ());
        domains::array_domain_traits<abs_dom_t>::array_load (m_inv, 
                                                             stmt.lhs ().name (), 
                                                             stmt.array ().name (), 
                                                             idx.name (),
                                                             stmt.elem_size());
      }
    }

    void exec (callsite_t &cs) {
      auto lhs_opt = cs.get_lhs_name ();
      if (lhs_opt) { // havoc 
        m_inv -= *lhs_opt;
      }
    }
  }; 

  //! Transformer specialized for computing numerical summaries
  template<typename SumTable, typename CallCtxTable /*unused*/>
  class bu_summ_num_abs_transformer: 
        public num_abs_transformer <typename SumTable::abs_domain_t,
                                   SumTable, CallCtxTable> {
                                   
   public:

    typedef typename SumTable::abs_domain_t summ_abs_domain_t;
    typedef typename CallCtxTable::abs_domain_t call_abs_domain_t;
    typedef summ_abs_domain_t abs_dom_t;

   public:

    typedef num_abs_transformer <abs_dom_t, SumTable, CallCtxTable> num_abs_transform_t;
    typedef typename num_abs_transform_t::abs_transform_t abs_transform_t;

    using typename abs_transform_t::varname_t;
    using typename abs_transform_t::z_var_t;
    using typename abs_transform_t::z_lin_exp_t;
    using typename abs_transform_t::z_bin_op_t;
    using typename abs_transform_t::z_assign_t;
    using typename abs_transform_t::z_assume_t;
    using typename abs_transform_t::z_select_t;
    using typename abs_transform_t::havoc_t;
    using typename abs_transform_t::unreach_t;
    using typename abs_transform_t::z_assert_t;
    using typename abs_transform_t::z_arr_init_t;
    using typename abs_transform_t::z_assume_arr_t;
    using typename abs_transform_t::z_arr_load_t;
    using typename abs_transform_t::z_arr_store_t;
    using typename abs_transform_t::callsite_t;

   private:

    SumTable* m_sum_tbl;

   public:

    static void reuse_summary (abs_dom_t& caller, 
                               const callsite_t& cs,
                               const typename SumTable::Summary& summ) {

      //crab::ScopedCrabStats st("Inter.ReuseSummary");      

      // --- meet caller's inv with summ
      auto sum_inv = summ.get_sum ();
      caller = caller & sum_inv;
      CRAB_LOG("inter",
               crab::outs() << "--- After meet: " <<  caller << "\n");
      // --- matching formal and actual parameters
      auto pars = summ.get_params ();
      unsigned i=0;
      std::set<varname_t> actuals, formals;
      for (auto p : pars) {
        auto a = cs.get_arg_name (i);
        if (!(a == p)) {
          caller += (z_var_t (a) == z_var_t (p));
        }
        ++i;
        actuals.insert (a); formals.insert (p);
      }
      // --- matching callsite's lhs and callee's return value 
      auto lhs_opt = cs.get_lhs_name ();
      auto ret_opt = summ.get_ret_val ();
      if (lhs_opt && ret_opt) {
        caller.assign(*lhs_opt, z_lin_exp_t (z_var_t (*ret_opt)));
        actuals.insert (*lhs_opt); formals.insert (*ret_opt);
      }
      CRAB_LOG ("inter", 
                crab::outs() << "--- After matching formals and actuals: " 
                <<  caller << "\n");
      // --- remove from caller only formal parameters so we can keep
      //     as much context from the caller as possible
      std::set<varname_t> s;
      boost::set_difference (formals, actuals, std::inserter(s, s.end ()));
      domains::domain_traits<abs_dom_t>::forget (caller, s.begin (), s.end ());
    }

   public:

    bu_summ_num_abs_transformer(abs_dom_t& inv, SumTable* sum_tbl)
        : num_abs_transform_t(inv), 
          m_sum_tbl (sum_tbl) { }
    
    bu_summ_num_abs_transformer(abs_dom_t& inv, SumTable* sum_tbl, CallCtxTable*)
        : num_abs_transform_t(inv), 
          m_sum_tbl (sum_tbl) { }

    abs_dom_t& inv () { return this->m_inv; }    

    void exec (z_bin_op_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_select_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_assign_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_assume_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (havoc_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (unreach_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_assert_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_arr_init_t &stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_assume_arr_t &stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_arr_store_t &stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_arr_load_t  &stmt) { num_abs_transform_t::exec (stmt); }

    // If there is a summary for the callee we use it to compute the
    // caller's summary
    void exec (callsite_t &cs) {
      if (!m_sum_tbl) {
        CRAB_WARN ("The summary table is empty: ignored analysis of callsite");
        return;
      }

      if (m_sum_tbl->hasSummary (cs)) {
        auto &sum = m_sum_tbl->get (cs);
        auto pars = sum.get_params ();
        if (pars.size () == cs.get_num_args ()) {
          reuse_summary (this->m_inv, cs, sum);
          return;
        }
        else
          CRAB_WARN ("Ignored callsite due to mismatch of caller and callee's parameters");
      }
      else
        CRAB_LOG("inter",
                 crab::outs() << "Summary not found for " << cs << "\n");
      
      auto lhs_opt = cs.get_lhs_name ();
      if (lhs_opt) { // havoc 
        this->m_inv -= *lhs_opt;
      }
    }
  }; 


  // Transformer specialized for performing top-down forward
  // traversal while reusing numerical summaries at the callsites
  template<typename SumTable, typename CallCtxTable>
  class td_summ_num_abs_transformer: 
        public num_abs_transformer<typename CallCtxTable::abs_domain_t,
                                  SumTable, CallCtxTable> {
                                   
   public:

    typedef typename SumTable::abs_domain_t summ_abs_domain_t;
    typedef typename CallCtxTable::abs_domain_t call_abs_domain_t;
    typedef call_abs_domain_t abs_dom_t;

   public:

    typedef num_abs_transformer<abs_dom_t, SumTable,CallCtxTable> num_abs_transform_t;
    typedef typename num_abs_transform_t::abs_transform_t abs_transform_t;

    using typename abs_transform_t::varname_t;
    using typename abs_transform_t::z_var_t;
    using typename abs_transform_t::z_lin_exp_t;
    using typename abs_transform_t::z_lin_cst_t;
    using typename abs_transform_t::z_lin_cst_sys_t;
    using typename abs_transform_t::z_bin_op_t;
    using typename abs_transform_t::z_assign_t;
    using typename abs_transform_t::z_assume_t;
    using typename abs_transform_t::z_select_t;
    using typename abs_transform_t::havoc_t;
    using typename abs_transform_t::unreach_t;
    using typename abs_transform_t::z_assert_t;
    using typename abs_transform_t::z_arr_init_t;
    using typename abs_transform_t::z_assume_arr_t;
    using typename abs_transform_t::z_arr_load_t;
    using typename abs_transform_t::z_arr_store_t;
    using typename abs_transform_t::callsite_t;

   private:

    typedef bu_summ_num_abs_transformer<SumTable,CallCtxTable> bu_abs_transformer_t;

    SumTable* m_sum_tbl;
    CallCtxTable* m_call_tbl;

   public:
    
    td_summ_num_abs_transformer (abs_dom_t& inv, 
                                 SumTable* sum_tbl, CallCtxTable* call_tbl)
        : num_abs_transform_t(inv), 
          m_sum_tbl (sum_tbl),
          m_call_tbl (call_tbl) { }
    
    abs_dom_t& inv () { return this->m_inv; }    
    
    void exec (z_bin_op_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_select_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_assign_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_assume_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (havoc_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (unreach_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_assert_t& stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_arr_init_t &stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_assume_arr_t &stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_arr_store_t &stmt) { num_abs_transform_t::exec (stmt); }
    void exec (z_arr_load_t  &stmt) { num_abs_transform_t::exec (stmt); }

    void exec (callsite_t &cs) {
      
      if (!m_sum_tbl) {
        CRAB_WARN ("The summary table is empty");
      }
      else if (m_sum_tbl->hasSummary (cs)) {
        
        auto &sum = m_sum_tbl->get (cs);
        auto pars = sum.get_params ();

        if (pars.size () == cs.get_num_args ()) {

          ///////
          /// Generate the callee context and store it.
          ///////
          abs_dom_t callee_ctx_inv (this->m_inv);
          // --- matching formal and actual parameters
          unsigned i=0;
          for (auto p : pars) {
            auto a = cs.get_arg_name (i);
            if (!(a == p)) {
              callee_ctx_inv += (z_var_t (p) == z_var_t (a));
            }
            ++i;
          }
          // --- project only onto formal parameters
          domains::domain_traits<abs_dom_t>::project (callee_ctx_inv, 
                                                      pars.begin (),
                                                      pars.end ());
          // --- store the callee context
          CRAB_LOG ("inter", 
                    crab::outs() << "--- Callee context stored: " 
                                 << callee_ctx_inv << "\n");
          m_call_tbl->insert (cs, callee_ctx_inv);          

          /////
          // Generate the continuation at the caller
          /////

          // --- convert this->m_inv to the language of summ_abs_dom_t (sum)
          summ_abs_domain_t caller_ctx_inv = summ_abs_domain_t::top();
          if (std::is_same<summ_abs_domain_t, abs_dom_t>::value) {
            caller_ctx_inv = this->m_inv;
          } else {
            // XXX: it will lose precision for disjunctive domains
            for (auto cst : this->m_inv.to_linear_constraint_system ())
              caller_ctx_inv += cst;
          }
          
          CRAB_LOG ("inter",
                    crab::outs() << "--- Caller context: " <<  caller_ctx_inv << "\n");
                    
          // --- reuse summary to do the continuation
          bu_abs_transformer_t::reuse_summary (caller_ctx_inv, cs, sum);
          CRAB_LOG ("inter",
                    crab::outs() << "--- Caller context after plugin summary: " 
                                 << caller_ctx_inv << "\n");

          // --- convert back inv to the language of abs_dom_t
          if (std::is_same<summ_abs_domain_t, abs_dom_t>::value) {
            this->m_inv = caller_ctx_inv;
          } else {
            // XXX: it will lose precision for disjunctive domains
            abs_dom_t inv = abs_dom_t::top();          
            for (auto cst : caller_ctx_inv.to_linear_constraint_system ())
              inv += cst;
            std::swap (this->m_inv, inv);
          }
          CRAB_LOG ("inter",
                    crab::outs() << "--- Caller continuation after " 
                                 <<  cs << "=" <<  this->m_inv << "\n");
          return;
        }
        else 
          CRAB_WARN ("mismatch of parameters between caller and callee");
      }
      else {
        // no summary found: do nothing
      }

      // We could not reuse a summary so we just havoc lhs of the call
      // site
      auto lhs_opt = cs.get_lhs_name ();
      if (lhs_opt) {
        this->m_inv -= *lhs_opt;
      }
    }
  }; 

  //! Abstract transformer specialized for pointer operations for
  //! only nullity information.
  template <typename VariableName,typename SumTable, typename CallCtxTable>
  class nullity_abs_transformer: public abs_transformer_api <VariableName>  {
    typedef abs_transformer_api<VariableName> abs_tr_t;
    
    using typename abs_tr_t::z_bin_op_t;
    using typename abs_tr_t::z_lin_cst_t;
    using typename abs_tr_t::z_var_t;
    using typename abs_tr_t::z_assign_t;
    using typename abs_tr_t::z_assume_t;
    using typename abs_tr_t::havoc_t;
    using typename abs_tr_t::unreach_t;
    using typename abs_tr_t::z_select_t;
    
    using typename abs_tr_t::callsite_t;
    using typename abs_tr_t::return_t;
    using typename abs_tr_t::ptr_load_t;
    using typename abs_tr_t::ptr_store_t;
    using typename abs_tr_t::ptr_assign_t;
    using typename abs_tr_t::ptr_object_t;
    using typename abs_tr_t::ptr_function_t;
    using typename abs_tr_t::ptr_null_t;
    using typename abs_tr_t::ptr_assume_t;
    using typename abs_tr_t::ptr_assert_t;
    
    typedef domains::nullity_domain <VariableName> nullity_domain_t;
    
    nullity_domain_t& m_inv;
    
   public:
    
    // for FwdAnalyzer.hpp
    typedef nullity_domain_t abs_dom_t;
    typedef nullity_domain_t summ_abs_domain_t;
    typedef nullity_domain_t call_abs_domain_t;
    
   public:
    
    nullity_abs_transformer (nullity_domain_t& init, SumTable*, CallCtxTable*):
        m_inv (init) { }

    nullity_domain_t& inv () { return m_inv; }

    void visit (ptr_null_t & stmt) { 
      m_inv.set (stmt.lhs (), domains::nullity_value::null ());
    }
    
    void visit (ptr_object_t & stmt) { 
      m_inv.set (stmt.lhs (), domains::nullity_value::non_null ());
    }
    
    void visit (ptr_function_t & stmt) { 
      m_inv.set (stmt.lhs (), domains::nullity_value::non_null ());
    }
    
    void visit (ptr_assign_t & stmt) { 
      m_inv.assign (stmt.lhs (), stmt.rhs ());
    }
    
    void visit (ptr_load_t & stmt) {
      m_inv.equality (stmt.rhs (), domains::nullity_value::non_null ());
    }
    
    void visit (ptr_store_t & stmt) { 
      m_inv.equality (stmt.lhs (), domains::nullity_value::non_null ());
    }
    
    void visit (ptr_assume_t& stmt) { 
      auto cst = stmt.constraint ();
      
      if (cst.is_tautology ()) {
        return;
      } 

      if (cst.is_contradiction ()) {
        m_inv = nullity_domain_t::bottom ();
        return;
      }

      if (cst.is_unary ()) {
        if (cst.is_equality ()) 
          m_inv.equality (cst.lhs (), domains::nullity_value::null ());
        else // cst.is_disequality ();
          m_inv.disequality (cst.lhs (), domains::nullity_value::null ());
      } else { 
        assert (cst.is_binary ());
        if (cst.is_equality ()) 
          m_inv.equality (cst.lhs (), cst.rhs ());
        else  // cst.is_disequality ();
          m_inv.disequality (cst.lhs (), cst.rhs ());
      }
    }
    
    void visit (callsite_t & stmt) { 
      // TODO
      if (auto lhs = stmt.get_lhs_name ()) {
        m_inv -= *lhs;
      }
    }
    
    void visit (havoc_t& stmt) {
      m_inv -= stmt.variable ();
    }
    
    void visit (unreach_t& stmt) { 
      m_inv = nullity_domain_t::bottom ();
    }
  };
  
  } // end namespace
} // end namespace
#endif 
