#include "UnitTest.hpp" // 其中include了Factor.hpp|CycleDiv.hpp

namespace Hasaki {

void UnitTestFactor() {
    cout << "------------------------------------------" << endl;
    cout << "Now unit test: Factor.hpp + Factor.cpp" << endl;
    cout << "Test content:  Function MyPow|MyPowMod" << endl;
    cout << "            :  Class    PrimePow|Factor" << endl;
    cout << "------------------------------------------" << endl;

    cout << "unit test1: uint32_t MyPow (uint32_t base, uint8 pow);" << endl;
    cout << MyPow(2, 31) << endl;         // expected: 2147483648
    cout << MyPow(3, 20) << endl;         // expected: 3486784401
    cout << MyPow(7, 10) << endl;         // expected: 282475249
    cout << MyPow(5, 1)  << endl;         // expected: 5
    
    cout << "unit test2: uint32_t MyPowMod (uint64_t base, uint32_t pow, uint32_t mod);" << endl;
    cout << MyPowMod(MAX32-2, 114514, MAX32)   << endl;   // expected: 262144
    cout << MyPowMod(10,      114514, 1919810) << endl;   // expected: 1199790
    cout << MyPowMod(114514,  1926,   817)     << endl;   // expected: 723
    cout << MyPowMod(13,      8,      1024)    << endl;   // expected: 33
    cout << MyPowMod(2,       31,     MAX32)   << endl;   // expected: 2147483648
    cout << MyPowMod(3,       20,     MAX32)   << endl;   // expected: 3486784401
    cout << MyPowMod(7,       10,     MAX32)   << endl;   // expected: 282475249
    cout << MyPowMod(5,       1,      MAX32)   << endl;   // expected: 5

    cout << "unit test3: PrimePow" << endl;
    PP    pp1(5, 3);
    PP    pp2(3, 2);
    cout << pp1 << endl;                        // expected: (5^3)
    cout << pp2 << endl;                        // expected: (3^2)

    cout << "unit test4: Factor" << endl;
    FT      ft1(2*2*3*5*7);
    FT      ft2(3486784401);
    cout << ft1 << endl;                        // expected: (2^2)(3^1)(5^1)(7^1)
    ft1.DispCalResult();                        // expected: 420 == (2^2)(3^1)(5^1)(7^1)
    ft2.DispCalResult();                        // expected: 3486784401 == (3^20)
    ft1.TryMultiple(pp1);
    ft1.DispCalResult();                        // expected: 52500 == (2^2)(3^1)(5^4)(7^1)
    ft2.TryMultiple(pp2);                       // expected: TryMultiple(pp) overflow，N=3486784401, pp=9
    ft2.DispCalResult();                        // expected: 3486784401 == (3^20)
    PP    pp3(5, 2);
    ft1.TryDiv(pp3);
    ft1.DispCalResult();                        // expected: 2100 == (2^2)(3^1)(5^2)(7^1)
    ft1.TryDiv(pp1);                            // expected: TryDiv(pp) dismatch，N=2100, pp=125
    ft1.DispCalResult();                        // expected: 2100 == (2^2)(3^1)(5^2)(7^1)
    ft1.TryDiv(pp3);
    ft1.DispCalResult();                        // expected: 84 == (2^2)(3^1)(7^1)
    ft2.TryMultiple(ft1);                       // expected: TryMultiple(pp) overflow，N=3486784401, pp=4
                                                // expected: TryMultiple(ft) overflow，N=3486784401, ft.m_N=84
    ft2.DispCalResult();                        // expected: 3486784401 == (3^20)
    FT      factor3(2*3*11);                      
    ft1.TryDiv(factor3);                        // expected: TryDiv(pp) dismatch，N=14, pp=11
                                                // expected: TryDiv(ft) dismatch，N=84, ft.m_N=66
    ft1.DispCalResult();                        // expected: 84 == (2^2)(3^1)(7^1)
}

void UnitTestNumber() {
    cout << "------------------------------------------" << endl;
    cout << "Now unit test: CycleDiv.hpp + CycleDiv.cpp" << endl;
    cout << "Test content:  Function Mod2and5|EulerPhi|CalOrd10T" << endl;
    cout << "------------------------------------------" << endl;
    uint32_t p1  = 0;
    Factor ft1 = Mod2and5(125, p1);
    ft1.DispCalResult();                        // expected: 1 ==
    std::cout << p1 << std::endl;               // expected: 3
    ft1 = Mod2and5(250, p1);
    ft1.DispCalResult();                        // expected: 1 ==
    std::cout << p1 << std::endl;               // expected: 3
    ft1 = Mod2and5(65535, p1);
    ft1.DispCalResult();                        // expected: 13107 == (3^1)(17^1)(257^1)
    std::cout << p1 << std::endl;               // expected: 1
    ft1 = Mod2and5(20, p1);
    ft1.DispCalResult();                        // expected: 1 ==
    std::cout << p1 << std::endl;               // expected: 2
    ft1 = Mod2and5(50, p1);
    ft1.DispCalResult();                        // expected: 1 =
    std::cout << p1 << std::endl;               // expected: 2
    ft1 = Mod2and5(4294967295, p1);
    ft1.DispCalResult();                        // expected: 858993459 = (3^1)(17^1)(257^1)(65537^1)
    std::cout << p1 << std::endl;               // expected: 1
    ft1 = Mod2and5(127, p1);
    ft1.DispCalResult();                        // expected: 127 == (127^1)
    std::cout << p1 << std::endl;               // expected: 0

    EulerPhi(2).DispCalResult();                // expected: 1 ==
    EulerPhi(3).DispCalResult();                // expected: 2 == (2^1)
    EulerPhi(4).DispCalResult();                // expected: 2 == (2^1)
    EulerPhi(2*2*2*3).DispCalResult();          // expected: 8 == (2^3)
    EulerPhi(3*3*3).DispCalResult();            // expected: 18 == (2^1)(3^2)
    EulerPhi(2*3*7).DispCalResult();            // expected: 12 == (2^2)(3^1)
    EulerPhi(2*2*3*7).DispCalResult();          // expected: 24 == (2^3)(3^1)
    EulerPhi(65535).DispCalResult();            // expected: 32768 == (2^15)
    EulerPhi(65537).DispCalResult();            // expected: 65536 == (2^16)
    EulerPhi(1000000007).DispCalResult();       // expected: 1000000006 == (2^1)(500000003^1)
    
    Factor ft2(63);
    ft2.DispCalResult();                        // expected: 63 == (3^2)(7^1)
    Factor ft3(EulerPhi(ft2.GetN()));
    ft3.DispCalResult();                        // expected: 36 == (2^2)(3^2)
    Factor ft4 = CalOrd10T(ft3, ft2.GetN());
    ft4.DispCalResult();                        // expected: 6 == (2^1)(3^1)
    Factor ft5(1000000007);
    ft5.DispCalResult();                        // expected: 1000000007 == (1000000007^1)
    Factor ft6(EulerPhi(ft5.GetN()));
    ft6.DispCalResult();                        // expected: 1000000006 == (2^1)(500000003^1)
    Factor ft7 = CalOrd10T(ft6, ft5.GetN());
    ft7.DispCalResult();                        // expected: 1000000006 == (2^1)(500000003^1)
    Factor ft8(9);
    ft8.DispCalResult();                        // expected: 9 == (3^2)
    Factor ft9(EulerPhi(ft8.GetN()));
    ft9.DispCalResult();                        // expected: 6 == (2^1)(3^1)
    Factor ft10 = CalOrd10T(ft9, ft8.GetN());
    ft10.DispCalResult();                       // expected: 1 ==
    Factor ft11(1);
    ft11.DispCalResult();                       // expected: 1 ==
    Factor ft12(EulerPhi(ft11.GetN()));
    ft12.DispCalResult();                       // expected: 1 ==
    Factor ft13 = CalOrd10T(ft12, ft11.GetN());
    ft13.DispCalResult();                       // expected: 1 ==
}

void UnitTestCycleDiv() {
    cout << "------------------------------------------" << endl;
    cout << "Now unit test: CycleDiv.hpp + CycleDiv.cpp" << endl;
    cout << "Test content:  Class    CycleDiv" << endl;
    cout << "------------------------------------------" << endl;

    std::vector<CycleDiv> vecCD = { CD(1,    7     ),   // expected: 1 / 7 == 0.[142857]
                                    CD(1,    896   ),   // expected: 1 / 896 == 0.0011160[714285]
                                    CD(1,    1792  ),   // expected: 1 / 1792 == 0.00055803[571428]
                                    CD(1,    3584  ),   // expected: 1 / 3584 == 0.000279017[857142]
                                    CD(1,    7168  ),   // expected: 1 / 7168 == 0.0001395089[285714]
                                    CD(1,    14336 ),   // expected: 1 / 14336 == 0.00006975446[428571]
                                    CD(1,    1     ),   // expected: 1 / 1 == 1.[0]
                                    CD(29,   14    ),   // expected: 29 / 14 == 2.0[714285]
                                    CD(0,    4     ),   // expected: 0 / 14 == 0.[0]
                                    CD(11,   1     ),   // expected: 11 / 1 == 11.[0]
                                    CD(100,  5     ),   // expected: 100 / 5 == 20.[0]
                                    CD(8,    512   ),   // expected: 8 / 512 == 0.015625[0]
                                    CD(4,    512   ),   // expected: 4 / 512 == 0.0078125[0]
                                    CD(2,    512   ),   // expected: 2 / 512 == 0.00390625[0]
                                    CD(1,    512   ),   // expected: 1 / 512 == 0.001953125[0]
                                    CD(1,    1000000007)
// expected: 1 / 1000000007 == 0.[0000000009999999930000000489999996570000024009999831930001176489991764570057648009596463932824752470...]
                                  };
    
    for (auto &cd : vecCD)
        cd.dispAllCyclicDecimal();

    // 显示最后一个CD(1,    1000000007)的用时
    (--vecCD.end())->dispTime();                        // expected: Process   time: 0ms
                                                        //           Malloc    time: 63ms
                                                        //           Calculate time: 125ms
}

} // namespace Hasaki

