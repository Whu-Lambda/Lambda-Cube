#ifndef FACTOR_HPP  // Factor.hpp
#define FACTOR_HPP

#include <iostream>
#include <set>                      // 用std::set
#include <cmath>                    // 用sqrt函数
#include <assert.h>                 // assert
#include <limits>                   // 用sqrt函数
#include <tuple>                    // 用std::tie

namespace Hasaki {

const   uint64_t    MAX32 = std::numeric_limits<uint32_t>::max();   // 4294967295

using   std::set;
using   std::tie;
using   std::cout;
using   std::endl;
using   std::ostream;

class   PrimePow;
class   Factor;
using   PP       =  PrimePow;               // typedef PrimePow PP
using   FT       =  Factor;                 // typedef Factor   FT
using   iterator =  set<PP>::iterator;

/**
 * @brief 计算整数乘方，不做结果越界检查，请小心
 * @param base  底数，范围为uint32_t
 * @param pow   乘方，要求pow>0，因为pow<32，故用uint8
 *              因为pow通常很小，这里不采用快速幂
 */
uint32_t MyPow (uint32_t base, uint8_t pow);

/**
 * @brief 计算(base^pow) % mod
 * @param base  底数（在本任务中，实际约定base=10）
 *              注意：要求该参数实际数据范围在uint32_t内！
 *              此处设置为uint64_t是为了防止溢出
 *              因为uint32_t * uint32_t < uint64_t
 * @param pow   乘方，一般是一个很大的数，所以要用快速幂
 * @param mod   模，一般是一个很大的数
 *              所以要求base和ans都用uint64_t储存，防止溢出
 */
uint32_t MyPowMod (uint64_t base, uint32_t pow, uint32_t mod);


/**
 * @brief PrimePow用于表示一个素数的m_prime的m_pow次幂。
 * 
 *        例如PrimePow(3, 5) == 3^5 == 243，m_pow不应当为0。
 *        本类主要作为质因数分解结果储存容器，不主动执行计算。
 *        因为不主动执行计算，所以假设总假设结果不越界
 */
class PrimePow {
private:
    uint32_t  m_prime;    // 素数
    uint8_t   m_pow;      // 该素数的幂

public:
    // 构造函数
    PrimePow() {};                                              // 空构造，别删！
    PrimePow(const PP &obj);                                    // copy构造
    PrimePow(uint32_t prime, uint8_t pow) : m_prime (prime)     // 赋值构造
                                          , m_pow   (pow) { }

    // 显示方法
    uint32_t ToInt    () const  {return MyPow(m_prime, m_pow);} // 假设结果不越界
    uint32_t GetPrime () const  {return m_prime;}
    uint8_t  GetPow   () const  {return m_pow;}
    void     SetPrime (uint32_t p){m_prime = p;}                // 该接口请小心使用

protected:    // 操作接口（因为该接口由上层Factor控制，溢出检查由上层执行，此处不做溢出检查）
    void    TryMultiple (const PP &pp);
    /**
     * @brief 如果除数和被除数pp相等，返回false，让上层接口Del该PrimePow对象
     */
    bool    TryDiv      (const PP &pp);

    // 小于操作符，用于给std::set判断重复元素，只判断prime，不判断pow！
    friend bool operator < (const PP &lhs, const PP &rhs) {
        if (lhs.m_prime < rhs.m_prime)
            return true;
        return false;
    }
    // 输出操作符
    friend ostream& operator << (ostream &os, const PP& pp) {
        os << "(" << pp.m_prime << "^" << (int)pp.m_pow << ")";
        return os;
    }

    // 将Factor作为友元类，从而Factor可以调用TryMultiple和TryDiv接口
    friend class Factor;
};

/**
 * @brief Factor类是质因数分解类。
 * 
 *        构造时只是将N传入，不参与计算，要求N不等于0，注意N非负！
 *        调用Factorization()后执行质因数分解，结果储存在m_factor中
 */
class Factor {
private:        // 数据成员
    uint32_t    m_N;            // 整数本身，记为N
    set<PP>     m_factor;       // 用set储存m_factor，保证O(log N)复杂度，虽然这里用不到，但后续好扩展

public:
    // 构造对象（不进行因式分解）
    Factor() {}             // 空构造，别删！
    Factor(const FT &obj);  // copy构造
    Factor(uint32_t N);     // 只构造对象，不因式分解，N不能为0

    // 显示方法，参数获取接口
    void            DispCalResult   () const;       // 显示N == 素因子形式
    uint32_t        GetN            () const    {return m_N;}
    const set<PP>&  GetPP           () const    {return m_factor;}
    void            SetN  (uint32_t N);             // 对N进行质因数分解，覆盖当前结果

    // 操作接口
    void            Factorization             ();   // 执行因式分解，结果储存到m_factor和m_len中
    bool            TryMultiple   (const PP &pp);   // 尝试乘以PrimePow类元素，溢出返回false
    bool            TryDiv        (const PP &pp);   // 尝试除以PrimePow类元素，不匹配返回false
    bool            TryMultiple   (const FT &ft);   // 尝试乘以Factor类元素，溢出返回false
    bool            TryDiv        (const FT &ft);   // 尝试除以Factor类元素，不匹配返回false

    // 输出操作符
    friend ostream& operator << (ostream &os, const FT& ft) {
        for (auto &pp : ft.m_factor)
            os << pp;
        return os;
    }
};

} // namespace Hasaki

#endif
