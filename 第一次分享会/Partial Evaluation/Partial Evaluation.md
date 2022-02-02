# PARTIAL  EVALUATION

作者：Lyzh流云坠海

## 什么是 Partial Evaluation

举个例⼦，正常的表达式求值过程：

```python
11+45+14
56+14
70
```

存在未知数的表达式求值流程:

```python
x+45+14
x+59
```

更多的例⼦：

- if <部分求值后确定的值> then a else b
- Code block

```rust
foo(a) // impure
let b = bar(x) // pure
foo(b) // impure
```

更复杂的情况……

- min(a, b) = if a < b then a else b
- min(min(3, x) 2) 

理想的展开结果：

min(2, x)

实际展开结果：

if (if 3 < x then 3 else x) < 2 then a else b



## Partial Evaluation是⼀个优化⼿段

更激进的Partial Evaluation魔法： The Futamura Projection。

![image-20220202225105807](.\image-20220202225105807.png)

![image-20220202225131267.png](.\image-20220202225131267.png)



简单的pass流程：

```haskell
// add const
def mulc(x,c) = cond {
    c.mod(2).eq(0) => x.lshift(c.log(2));
    true => x.raw_mul(c);
}
```

解释器的规约流程:

- value => value
- access structure => struct.get_field(name)
- symbol => lookup env get value
- primitive add => a.primitive_add(b)
- etc

![image-20220202225409758](.\image-20220202225409758.png)







