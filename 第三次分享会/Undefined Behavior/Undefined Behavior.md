# Undefined Behavior

## 未定义⾏为是什么？

特定场景下，语⾔标准明确声明对该处的语义不做任何要求。

从实际⽤途/危害来看，它可以是 

- 语⾔设计者⼿头的强⼒⼯具 
- ⽣成奇异bug的反应炉 
- 程序优化的有⼒假设 
- 语⾔本⾝潜在的致病基因

## 概览

C99中的经典UB(但是⼀共有191个) 

- 有符号整型溢出 
- 除以0 
- 修改const修饰类型的对象 
- 违反类型规则(如将⼀个 `int *` 转换为 `float*`) 
- 解引⽤空指针 解引⽤悬垂指针/数组访问越界 
- 使⽤未初始化的变量 
- 超出⼤⼩的移位运算 

 C11定义了Memory Model后新增的⼀些UB 

- 程序执⾏时的数据竞争 
- 访问Atomic结构/联合的成员



## 例⼦：bzip2中的⼦串⽐较函数

此例⼦出于CppCon2016的talk“Garbage in, Garbage Out：Arguing about Undefined Behavior With Nasal Demons” 

出⾃bzip2的源码(blocksort.c, 名字叫mainGtU)

```c
bool compare(uint32_t i1, uint32_t i2, uint8_t *block) {
uint8_t c1, c2
// 在⼀个循环中
c1 = block[i1]; c2 = block[i2];
if(c1 != c2) return (c1 > c2);
i1++; i2++;
}
```

也许你会想，数组下标就应该是⾮负的，所以uint32_t没问题 

但是此处⽤int32_t在X86-64平台上可避免因处理潜在溢出⽽加⼊的截断 

⽣成的汇编只有原本的⼆分之⼀

## 例⼦：GCC的⻤故事

涉及strict aliasing

```c
// linux/include/net/iw_handler.h
static inline iwe_stream_add_event(char * stream, // Stream of events
char * ends, // End of Stream
struct iw_event * iwe, // Payload
int event_len) // Real size of Payload
{
    if((stream + event_len) < ends) {
        iwe->len = event_len;
        memcpy(stream, (char *) iwe, event_len); // A1
        stream += event_len; // A2
    }
}
```

GCC看起来毫⽆道理地调换了A1和A2的顺序 实情：Linux内核的memcpy是个宏，将⼤块数据cast为 `long *` 进⾏复制

## 例⼦：Linux内核net/tun实现

[https://isc.sans.edu/diary/A+new+fascinating+Linux+kernel+vulnerability/6820](https://isc.sans.edu/diary/A+new+fascinating+Linux+kernel+vulnerability/6820)

发现者：Bojan Zdrnja，⽇期：2009 - 07 17 

```c
struct sock* sk = tun->sk;
// tun有可能为NULL
// ......
if(!tun)
return POLLRR
```

GCC在编译之后将if块整个删去了

另一例：[Red Hat Crash Utility — crash error out with kernel dump with "cgroup.memory=nokmem" (spinics.net)](https://www.spinics.net/linux/fedora/redhat-crash-utility/msg08514.html)

## 与未定义⾏为共处

- 静态分析⼯具 
- 启⽤编译器警告 
- 使⽤编译器⽀持的动态检查

例：Clang和gcc都⽀持-ftrapv这个选项，可开启对有符号整型的溢出检查 

说多点，这个检查让溢出的⾏为固定，但是对INT_MIN / -1没⽤ 

Clang的-fcatch-undefined-behavior可提供⼀些简单的动态检查

- 使⽤Valgrind等提供额外动态检查的⼯具
- 使⽤推理

[接口即泛型 - SegmentFault 思否](https://segmentfault.com/a/1190000004250754)

POSIX.1-2001标准规定的dlsym函数依赖于void指针与函数指针的转换 

虽然这是个UB，但是在符合POSIX.1-2001标准的系统上，转换是安全的

