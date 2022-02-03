#include "CycleDiv.hpp" // 其中include了Factor.hpp
#include <windows.h>    // 获取计时

namespace Hasaki {

/****** Mod2and5|EulerPhi|CalOrd10T|GCD 函数 ******/

FT Mod2and5 (uint32_t N, uint32_t& p) {
    const FT    tmpN(N);    // 遍历用，禁止改变值，否则for range会炸
          FT    tmpT(N);    // 返回值

    uint8_t     counter2 = 0;
    uint8_t     counter5 = 0;
    uint32_t    tmpPrime;

    for (auto &pp : tmpN.GetPP()) {     // 除以2^s1
        tmpPrime = pp.GetPrime();
        if (tmpPrime == 2) {
            counter2 = pp.GetPow();
            tmpT.TryDiv(pp);
        }
    }

    for (auto &pp : tmpN.GetPP()) {     // 除以5^s2
        tmpPrime = pp.GetPrime();
        if (tmpPrime == 5) {
            counter5 = pp.GetPow();
            tmpT.TryDiv(pp);
        }
    }

    p = (uint32_t)(counter2 > counter5 ? counter2 : counter5);
    return tmpT;
}

FT EulerPhi (const FT& t) {
    FT      tmpT(t);
    FT      tmpMult;                // 空Factor
    set<PP> setPP;   // 存(p1^1)到(pn^1)

    // 把每个因子取出来一个，放到pp
    for (auto pp : tmpT.GetPP())
        setPP.emplace( PP(pp.GetPrime(), 1) );
    
    // 除掉每个pp
    for (auto &pp : setPP)
        tmpT.TryDiv(pp);
    
    // 乘以每个(pp[k]-1)
    for (auto &pp : setPP) {
        tmpMult.SetN(pp.ToInt() - 1);
        tmpT.TryMultiple(tmpMult);
    }

    return tmpT;
}

Factor CalOrd10T (const Factor &ft, uint32_t mod) {
    FT      tmpFT(ft);
    PP      tmpPP(1, 1);                // 工具人变量，m_prime会变
    uint8_t nowPow;                     // 因为是while(nowPow--)，所以可以unsigned

    for (auto &pp : ft.GetPP()) {
        tmpPP.SetPrime(pp.GetPrime());  // 相当于tmpPP = PP(pp.GetPrime(), 1);
        nowPow = pp.GetPow();

        while (nowPow--) {              // 如果nowPow自减前为0，说明该因子已经算完了
            tmpFT.TryDiv(tmpPP);
            if (MyPowMod(10, tmpFT.GetN(), mod) == 1)   // 如果余数为1，那么继续除以自己
                continue;
            else {                      // 意味着这个因子除完了，该下一个因子了
                tmpFT.TryMultiple(tmpPP);
                break;
            }
        }
    }

    return tmpFT;
}

inline uint32_t GCD(uint32_t a,uint32_t b) {
    return b>0 ? GCD(b, a % b):a;
}

/****** CycleDiv 类 ******/

ostream& operator << (ostream &os, const CD& cd) {
    uint32_t    tmpP = cd.m_loopP;
    uint32_t    tmpQ = cd.m_loopQ > MAX_OUTPUT ? MAX_OUTPUT : cd.m_loopQ; // 最大只显示100位

    os << cd.m_M / cd.m_N << ".";               // 整数部分

    uint32_t k = 0;

    for (k = 0; k < tmpP / 8; ++k)    // 非循环小数的部分1
        os << setw(8) << setfill('0') << (uint32_t) cd.m_decimal[k];

    if (tmpP % 8)                     // 非循环小数的部分2
        os << setw(tmpP % 8) << setfill('0') << (cd.m_decimal[k] / MyPow(10, 8 - tmpP % 8));
    
    os << "[";

    if (tmpP / 8 == tmpQ / 8)
        os << setw(tmpQ - tmpP) << setfill('0') 
           << (cd.m_decimal[k] / MyPow(10, 8 - tmpQ % 8) % MyPow(10, tmpQ - tmpP));
    else {
        os << setw(8 - tmpP % 8) << setfill('0') << (cd.m_decimal[k] % MyPow(10, 8 - tmpP % 8));

        for (++k; k < tmpQ / 8; ++k)
            os << setw(8) << setfill('0') << (uint32_t) cd.m_decimal[k];

        if (tmpQ % 8)
            os << setw(tmpQ % 8) << setfill('0') << (cd.m_decimal[k] / MyPow(10, 8 - tmpQ % 8));
    }
    
    if (tmpQ != cd.m_loopQ)         // 如果被截断为了MAX_OUTPUT，输出...
        os << "...";
    
    os << "]" << endl;
    return os;
}

CycleDiv::CycleDiv (uint32_t M, uint32_t N)
    : m_M (M)               // m_N = N; m_M = M;
    , m_N (N) {

    assert(N != 0);                             // 分母不能为0

    ULONGLONG time_start = GetTickCount64();    // 计时
    
    M = M % N;                                  // 只需要计算小数部分
    uint32_t tmpGCD = (M == 0 ? N : GCD(N, M));
    M /= tmpGCD;                                // 除掉公因数
    N /= tmpGCD;
    
    // 正式开始计算
    FT tmpT  = Mod2and5(N, m_loopP);    // N == (2^s1)(5^s2)(t), m_loopP计算完后会被赋值为max{s1, s2}！
    FT tmpEP = EulerPhi(tmpT);   // tmpEP = EulerPhi(t)
    m_loopQ  = m_loopP + CalOrd10T(tmpEP, tmpT.GetN()).GetN();

    uint32_t loopLen = (m_loopQ / 8) + 1;  // 因为一个数储存8位十进制小数，所以只算1/8长度

    m_preTime = GetTickCount64() - time_start;  // 计算预处理时间
    time_start = GetTickCount64();

    m_decimal.resize(loopLen);                  // 这句话有点费时间

    m_vecTime = GetTickCount64() - time_start;  // 计算空间分配时间
    time_start = GetTickCount64();

    // 定义计算小数的lambda函数，方便多线程
    auto calDecimal = [&](uint64_t M, uint64_t N, uint32_t p, uint32_t q) {
        M = M * (uint64_t)MyPowMod(100000000, p, N) % N;  // M = M * (10^(8p) % N)

        for (; p != q; ++p) {
            M *= 100000000;
            m_decimal[p] = M / N;
            M %= N;
        }
    };
    
    if (loopLen < 100)      // 比较小的就没必要用多线程加速了
        calDecimal(M, N, 0, loopLen);
    else {
        uint16_t        thread_num = 16;

        vector<thread>  threads;
        vector<uint32_t> pAndq;         // 装loopP和loopQ的容器，用于指导多线程分片

        for (uint16_t i = 0; i <= thread_num; ++i)  // (i, i+1) == (p_i, q_i)
            pAndq.emplace_back((uint64_t)loopLen * (uint64_t)i / (uint64_t)thread_num);
        
        for (uint16_t i = 0; i <  thread_num; ++i)
            threads.emplace_back( thread(calDecimal, M, N, pAndq[i], pAndq[i+1]) );
        
        for (auto &tr : threads)
            tr.join();
    }

    m_calTime = GetTickCount64() - time_start;   // 计算部分时间
}

} // namespace Hasaki
