/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    dd_pdd.cpp

Abstract:

    Poly DD package 

Author:

    Nikolaj Bjorner (nbjorner) 2019-12-24
    Lev Nachmanson (levnach) 2019-12-24

Revision History:

--*/
#pragma once

#include "math/dd/dd_pdd.h"
#include "math/interval/dep_intervals.h"
#include "util/scoped_ptr_vector.h"

namespace dd {
typedef dep_intervals::interval interval;
typedef dep_intervals::with_deps_t w_dep;
// calculates the interval of a pdd expression based on the given intervals of the variables
class pdd_interval {
    dep_intervals& m_dep_intervals;
    std::function<void (unsigned, bool, scoped_dep_interval&)> m_var2interval;
    std::function<void (unsigned, bool, scoped_ptr_vector<scoped_dep_interval>&)> m_var2intervals;

    // retrieve intervals after distributing multiplication over addition.
    template <w_dep wd>
    void get_interval_distributed(pdd const& p, scoped_dep_interval& i, scoped_dep_interval& ret) {
        bool deps = wd == w_dep::with_deps;
        if (p.is_val()) {
            if (deps)
                m_dep_intervals.mul<dep_intervals::with_deps>(p.val(), i, ret);
            else
                m_dep_intervals.mul<dep_intervals::without_deps>(p.val(), i, ret);
            return;
        }
        scoped_dep_interval hi(m()), lo(m()), t(m()), a(m());
        get_interval_distributed<wd>(p.lo(), i, lo);
        m_var2interval(p.var(), deps, a);
        if (deps) {
            m_dep_intervals.mul<dep_intervals::with_deps>(a, i, t);
            get_interval_distributed<wd>(p.hi(), t, hi);
            m_dep_intervals.add<dep_intervals::with_deps>(hi, lo, ret);
        }
        else {
            m_dep_intervals.mul<dep_intervals::without_deps>(a, i, t);
            get_interval_distributed<wd>(p.hi(), t, hi);
            m_dep_intervals.add<dep_intervals::without_deps>(hi, lo, ret);
        }
    }

public:
    
    pdd_interval(dep_intervals& d): m_dep_intervals(d) {}

    dep_intervals& m() { return m_dep_intervals; }

    std::function<void (unsigned, bool, scoped_dep_interval&)>& var2interval() { return m_var2interval; } // setter
    const std::function<void (unsigned, bool, scoped_dep_interval&)>& var2interval() const { return m_var2interval; } // getter

    std::function<void (unsigned, bool, scoped_ptr_vector<scoped_dep_interval>&)>& var2intervals() { return m_var2intervals; } // setter
    const std::function<void (unsigned, bool, scoped_ptr_vector<scoped_dep_interval>&)>& var2intervals() const { return m_var2intervals; } // getter

    template <w_dep wd>
    void get_interval(pdd const& p, scoped_dep_interval& ret) {
        if (p.is_val()) {
            m_dep_intervals.set_interval_for_scalar(ret, p.val());
            return;
        }
        bool deps = wd == w_dep::with_deps;
        scoped_dep_interval hi(m()), lo(m()), t(m()), a(m());
        m_var2interval(p.var(), deps, a);
        get_interval<wd>(p.hi(), hi);
        get_interval<wd>(p.lo(), lo);
        if (deps) {
            m_dep_intervals.mul<dep_intervals::with_deps>(hi, a, t);
            m_dep_intervals.add<dep_intervals::with_deps>(t, lo, ret);
        } else {
            m_dep_intervals.mul(hi, a, t);
            m_dep_intervals.add(t, lo, ret);
        }
    }

    template <w_dep wd>
    void get_interval_distributed(pdd const& p, scoped_dep_interval& ret) {
        scoped_dep_interval i(m());
        m_dep_intervals.set_interval_for_scalar(i, rational::one());        
        get_interval_distributed<wd>(p, i, ret);
    }

    //
    // produce an explanation for a range using weaker bounds.
    //
    // lo_interval := interval(lo)
    // hi_bound    := bound - lo_interval
    // hi_interval := explain(var*hi, hi_bound);
    // lo_bound    := bound - hi_interval
    // lo_interval := explain(lo, lo_bound);
    // return lo_interval + hi_interval
    // 
    void explain(pdd const& p, interval const& bound, scoped_dep_interval& ret) {
        if (p.is_val()) {
            m_dep_intervals.set_interval_for_scalar(ret, p.val());
            return;
        }
        scoped_dep_interval a(m()), t(m()), hi(m()), lo(m());
        scoped_dep_interval lo_interval(m()), lo_bound(m());
        scoped_dep_interval hi_interval(m()), hi_bound(m());
        if (!p.hi().is_val()) {
            m_var2interval(p.var(), true, a);
            get_interval<w_dep::with_deps>(p.hi(), hi);
            m_dep_intervals.mul<dep_intervals::with_deps>(hi, a, hi_interval);
            m_dep_intervals.sub(bound, hi_interval, lo_bound);
            explain(p.lo(), lo_bound, lo_interval);
        }
        else { 
            // lo_B + coeff*v : bounds
            // v in (bounds - l_B) / coeff
            
            get_interval<w_dep::without_deps>(p.lo(), lo_interval);
            m_dep_intervals.sub(bound, lo_interval, hi_bound);
            m_dep_intervals.div(hi_bound, p.hi().val().to_mpq(), hi_bound);
            scoped_ptr_vector<scoped_dep_interval> var_intervals;
            scoped_dep_interval var_interval(m());
            m_var2intervals(p.var(), true, var_intervals);
            for (auto* vip : var_intervals) {
                auto & vi = *vip;
                if (!m_dep_intervals.lower_is_inf(vi) && !m_dep_intervals.lower_is_inf(hi_bound) && rational(m_dep_intervals.lower(vi)) > m_dep_intervals.lower(hi_bound)) {
                    if (m_dep_intervals.lower_is_inf(var_interval) || m_dep_intervals.lower(vi) > m_dep_intervals.lower(var_interval)) {
                        m_dep_intervals.set_lower(var_interval, m_dep_intervals.lower(vi));
                        m_dep_intervals.set_lower_dep(var_interval, m_dep_intervals.lower_dep(vi));                        
                    }
                }
                if (!m_dep_intervals.upper_is_inf(vi) && !m_dep_intervals.upper_is_inf(hi_bound) && m_dep_intervals.upper(hi_bound) > m_dep_intervals.upper(vi)) {
                    if (m_dep_intervals.upper_is_inf(var_interval) || m_dep_intervals.upper(var_interval) > m_dep_intervals.upper(vi)) {
                        m_dep_intervals.set_upper(var_interval, m_dep_intervals.upper(vi));
                        m_dep_intervals.set_upper_dep(var_interval, m_dep_intervals.upper_dep(vi));                        
                    }
                }
            }
            m_dep_intervals.mul(var_interval, p.hi().val().to_mpq(), hi_interval);
            m_dep_intervals.sub(bound, hi_interval, lo_bound);            
            explain(p.lo(), lo_bound, lo_interval);
        }
        m_dep_intervals.add<dep_intervals::with_deps>(lo_interval, hi_interval, ret);
    }
};
}
