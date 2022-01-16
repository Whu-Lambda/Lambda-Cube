#include "UnitTest.hpp"
#include <fstream>

int main() {
    Hasaki::UnitTestFactor();
    Hasaki::UnitTestNumber();
    Hasaki::UnitTestCycleDiv();

    // 如果想要输出到文件，请使用下面这一段被注释掉的代码
    // 然后把CycleDiv.hpp的第12行改成下面这一行，以输出所有小数位
    // #define MAX_OUTPUT  MAX32

    /*
    std::ofstream output1;
    output1.open("D:/Desktop/ans/1_1000000007.txt");
    Hasaki::CD cd1(1, 1000000007);

    ULONGLONG time_start = GetTickCount64();    // 计时

    output1 << cd1;

    std::cout << "Print time: " << GetTickCount64() - time_start << "ms" << std::endl;  // 打印会很慢，懒得优化了
    */

    getchar();
    return 0;
}


