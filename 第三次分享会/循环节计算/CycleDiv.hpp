#ifndef CYCLEDIV_HPP  // CycleDiv.hpp
#define CYCLEDIV_HPP

#include "Factor.hpp"
#include <iomanip>      // 输出补0
#include <vector>       // 输出补0
#include <windows.h>    // 获取计时
#include <thread>       // 多线程

namespace Hasaki {

#define MAX_OUTPUT  100     // 为了显示方便，要求最大只显示MAX_OUTPUT位数

class   CycleDiv;
using   CD       =  CycleDiv;               // typedef CycleDiv CD

using   std::setw;
using   std::setfill;
using   std::vector;
using   std::thread;

/**
 * @brief 设N=(2^s1)(5^s2)t
 *        除掉所有因子2^s1和5^s2，返回引用p=max{s1, s2}
 *        返回Factor t
 */
FT Mod2and5 (uint32_t N, uint32_t& p);

/**
 * @brief 计算整数T的EulerPhi(T)，返回一个Factor类型
 *        设T=(p1^{s1})*...(pn^{sn})
 *        EulerPhi(T)=(p1^{s1-1})*...(pn^{sn-1})(p1-1)...(pn-1)
 */
FT EulerPhi (const FT& t);

/**
 * @brief 计算ord10t
 *        设EulerPhi(t)=(p1^s1)(p2^s2)...(pn^sn)=s
 *        减少s1，计算10^s(mod t)，直到再少后10^s(mod t)不为1为止（记此时为a1）
 *        减少s2到a2，同样的操作，做完就s3，一直到sn
 *        返回(p1^a1)(p2^a2)...(pn^an)
 */
Factor CalOrd10T (const Factor &ft, uint32_t mod);

/**
 * @brief 辗转相除法求公因子，输入可以有0
 */
inline uint32_t GCD(uint32_t a,uint32_t b);

/**
 * @brief CycleDiv类是计算循环除法的类，要求分母不为0，输入参数非负
 * 
 *        该类首先通过数论求阶的方法计算出m_loopP和m_loopQ
 *        然后通过乘10^n法求余的办法求出每一位的十进制值
 */
class CycleDiv{
public:
    CycleDiv(uint32_t M, uint32_t N);                   // 构造对象，并执行计算

    void dispAllCyclicDecimal() const {cout << m_M << " / " << m_N << " == " << *this;};     // 显示分子+分母+该分数的循环小数形式
    void      dispTime       () const {cout << "Process   time: " << m_preTime << "ms" << endl
                                            << "Malloc    time: " << m_vecTime << "ms" << endl
                                            << "Calculate time: " << m_calTime << "ms" << endl;}   // 返回m_time
    uint32_t  getM           () const {return m_M;}                     // 返回m_M
    uint32_t  getN           () const {return m_N;}                     // 返回m_N
    uint32_t  getP           () const {return m_loopP;}                 // 返回m_loopP
    uint32_t  getQ           () const {return m_loopQ;}                 // 返回m_loopQ
    uint32_t  getLoopLength  () const {return m_loopQ - m_loopP;}       // 返回(m_loopQ - m_loopP)，即循环节长度
    uint32_t  GetDecimal (uint32_t N) const{return m_decimal[N];}

private:
    ULONGLONG        m_preTime; // 预处理时长
    ULONGLONG        m_vecTime; // 分配空间时长
    ULONGLONG        m_calTime; // 计算时长
    uint32_t         m_M;       // M
    uint32_t         m_N;       // N
    vector<uint32_t> m_decimal; // 小数部分，每个储存8位十进制小数
    uint32_t         m_loopP;   // 循环节范围(m_loopP, m_loopQ]
    uint32_t         m_loopQ;

    // 输出操作符
    friend ostream& operator << (ostream &os, const CD& cd);
};

} // namespace Hasaki

#endif
