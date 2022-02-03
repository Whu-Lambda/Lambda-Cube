#include "Factor.hpp"

namespace Hasaki {

/****** MyPow|MyPowMod 函数 ******/

uint32_t MyPow (uint32_t base, uint8_t pow) {
    uint32_t ans = base;

    for (uint8_t i = 1; i < pow; ++i) 
        ans *= base;
    
    return ans;
}

uint32_t MyPowMod (uint64_t base, uint32_t pow, uint32_t mod) {
    uint64_t ans    = 1;

    while (pow > 0) {
        if (pow & 1)        // 相当于if pow % 2 == 1
            ans = (ans * base) % mod;
        
        base = (base * base) % mod;
        pow >>= 1;          // 相当于pow /= 2;
    }
    return (uint32_t)ans;
}

/****** PrimePow 类 ******/

PrimePow::PrimePow(const PP &obj) {
    m_prime  =  obj.m_prime;
    m_pow    =  obj.m_pow;
}

void PrimePow::TryMultiple (const PP &pp) {
    m_pow += pp.m_pow;
}

bool PrimePow::TryDiv (const PP &pp) {
    // 底数不匹配或被除数的pow比除数的pow小则返回false
    if (m_pow != pp.m_pow) {
        m_pow -= pp.m_pow;
        return true;
    }
    else
        return false;
}

/****** Factor 类 ******/

Factor::Factor(const FT &obj) {
    m_N      = obj.m_N;
    m_factor = set<PP>(obj.m_factor);
}

Factor::Factor (uint32_t N) {
    assert(N != 0);     // 可以允许N == 1，1的m_factor是空集合

    m_N   = N;
    Factor::Factorization ();
}

void Factor::SetN (uint32_t N) {
    assert(N != 0);     // 可以允许N == 1，1的m_factor是空集合

    m_N   = N;
    m_factor.clear();
    Factor::Factorization ();
}

void Factor::DispCalResult () const {
    cout << m_N << " == " << *this << endl;
}

void Factor::Factorization () {
    if (m_factor.size() != 0)
        m_factor.clear();

    uint32_t  N       = m_N;
    uint32_t  sqrtN   = sqrt(N);
    uint8_t   counter = 0;

    while (N % 2 == 0) {                // 单独算2，这样就只用判断奇数了
        N /= 2;
        ++counter;
    }
    if (counter != 0) {
        m_factor.emplace( PP(2, counter) );
        sqrtN = sqrt(N);
    }

    counter = 0;
    for (uint32_t k = 3;k <= sqrtN;k += 2) {  // 只判断奇数
        if (N % k == 0) {               // 如果k是因子
            while (N % k == 0) {
                N /= k;
                ++counter;
            }
            m_factor.emplace( PP(k, counter) );
            sqrtN = sqrt(N);
            counter = 0;
        }
    }
    if (N != 1)                         // 如果N不能整除sqrt(N)及以下的数，那么N是素数
        m_factor.emplace( PP(N, 1) );
}

bool Factor::TryMultiple (const PP &pp) {
    if ((uint64_t)m_N * (uint64_t)pp.ToInt() > MAX32) { // 溢出
        cout << "TryMultiple(pp) overflow，N=" << m_N << ", pp=" << pp.ToInt() << endl;
        return false;
    }
    
    m_N *= pp.ToInt();

    iterator    it;
    bool        isSuccess;
    tie(it, isSuccess) = m_factor.insert(pp);

    if ( !isSuccess ) {             // 如果插入失败，说明有重复元素了，对重复元素执行TryMultiple
        auto   &lhs = const_cast<PP&>(*it);
        lhs.TryMultiple(pp);
    }
    
    return true;
}


bool Factor::TryDiv (const PP &pp) {
    iterator    it;
    it = m_factor.find(pp);

    if (it == m_factor.end() || (*it).m_pow < pp.m_pow) {   // 如果没找到因子，或者被除数的幂小于除数
        cout << "TryDiv(pp) dismatch，N=" << m_N << ", pp=" << pp.ToInt() << endl;
        return false;
    }

    m_N /= pp.ToInt();
    auto   &lhs = const_cast<PP&>(*it);
    if( !lhs.TryDiv(pp) ) {              // 返回false意味着删除该节点
        m_factor.erase(it);
    }
    
    return true;
}

bool Factor::TryMultiple (const FT &ft) {
    for (auto it = ft.m_factor.begin(); it != ft.m_factor.end(); ++it) {
        if ( !TryMultiple(*it) ) {       // 如果有乘法溢出，就不必再算了
            for (auto it2 = ft.m_factor.begin(); it2 != it; ++it2)  // 把原来乘的都除回去，以复原
                TryDiv(*it2);
            cout << "TryMultiple(ft) overflow，N=" << m_N << ", ft.m_N=" << ft.m_N << endl;
            return false;
        }
    }
    
    return true;
}

bool Factor::TryDiv (const FT &ft) {
    for (auto it = ft.m_factor.begin(); it != ft.m_factor.end(); ++it) {
        if ( !TryDiv(*it) ) {       // 如果有除法溢出，就不必再算了
            for (auto it2 = ft.m_factor.begin(); it2 != it; ++it2)  // 把原来除的都乘回去，以复原
                TryMultiple(*it2);
            cout << "TryDiv(ft) dismatch ，N=" << m_N << ", ft.m_N=" << ft.m_N << endl;
            return false;
        }
    }
    
    return true;
}

} // namespace Hasaki
