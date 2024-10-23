---
weight: 3
title: "逻辑综合与 Design Compiler "
description: "逻辑综合与 Design Compiler "
draft: true

---

### 1. 综合综述

#### 1.1 什么是综合

综合是在满足设计电路的功能、速度及面积等限制条件下，将行为描述的或 RTL 级的电路转换为指定的技术库中单元电路的连接（门级电路）。

> **Synthesis = Translation + Optimization + Mapping**

综合主要包括三个阶段：转换、映射与优化。综合工具首先将 HDL 代码转换成一个 GTECH 网表(通用布尔逻辑，与工艺无关)，然后根据具体指定的工艺库，将 GTECH 网表映射到工艺库上，成为一个门级网表，最后再根据设计者施加的诸如延时、面积方面的约束条件，对门级网表进行优化。

#### 1.2 RTL 级综合

在 RTL 级综合中，电路的数学运算和行为功能分别通过 HDL 语言特定的运算符和行为结构描述出来。对于时序电路，我们可以明确的描述它在每个时钟边沿的行为。下面是一个加法器的描述：

```
module INCREMENT (A, CLOCK, Z);
    input [0:2] A;
    input CLOCK;
    output [0:2] Z;
    reg [0:2] Z;

    always @(posedge CLOCK)
        Z <= A + 1;
endmodule
```

它综合以后的网表如下图所示：

![rtl_synthesis](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/rtl_synthesis.png)

注意到，上图中的三个触发器不是例化而是通过 HDL 的特定结构推断出来的。这种推
断是根据一些推断法则进行的，例如在这个例子中，当一个信号（变量）在
时钟的边沿进行赋值（always 语句），那么这个信号（变量）可以推断为一个触发器。

除了 RTL 级综合，还有逻辑级综合、行为级综合，它们不在本文讨论范围之内。本文中所提到的 Design Compiler 是 Synopsys 公司的 RTL 级综合工具。

#### 1.3 Design Compiler 综合流程

![dc_flow](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/dc_flow.png)

与一般的综合过程相同，使用 DC 做综合也包含转换、优化和映射三个阶段。转换阶段
综合工具将 HDL 语言描述的电路或未映射的电路用工艺独立的 RTL 级的逻辑来实现，对于
Synopsys 的综合工具 DC 来说，就是使用 gtech.db 库中的 RTL 级单元来组成一个中间的网
表。优化与映射是综合工具对已有的中间网表进行分析，去掉其中的冗余单元，并对不满足
限制条件(如 constraints.tcl)的路径进行优化，然后将优化之后的电路映射到由制造商提供的
工艺库上(如 core_slow.db)。


### 2. Verilog 语言结构到门级的映射

#### 2.1 always 语句的综合

always 语句用来描述电路的过程行为(procedural behavior)，表示当事件列表中的状态发
生变化时，执行语句体中的语句。下面是一个包含过程赋值的 always 语句的例子。

```
module EvenParity(A, B, C, D, Z);
    input A, B, C, D;
    output Z;
    reg Z, Temp1, Temp2;

    always @(A or B or C or D)
    begin 
        Temp1 = A ^ B;
        Temp2 = C ^ D;
        Z = Temp1 ^ Temp2;
    end
```

电路综合后的网表如下所示：

![always](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/always.png)

使用 always 语句描述组合电路要注意的是：在该语句中读入的所有变量都需要出现在事件列表中(对 Verilog 语言而言是指“@”符号之后的信号)，否则可能会得不到用户期望的结
果。

#### 2.2 if 语句的综合

if 语句用于描述受条件控制的电路，下面是一个例子：
```
module SimpleALU (Ctrl, A, B, Z);
    input Ctrl;
    input [0:1] A, B;
    output [0:1] Z;
    reg [0:1] Z;

    always @ (Ctrl or A or B)
        if (Ctrl)
            Z = A & B;
        else 
            Z = A | B;
endmodule
```

![if1](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/if1.png)


如果在使用 if 语句时，没有指出条件判断的所有可能情况，则会在电路中引入锁存器（Latch），如下例所示

```
module Compute (Marks, Grade);
    input [1:4] Marks;
    output [0:1] Grade;
    reg [0:1] Grade;
    parameter FAIL = 1, PASS = 2, EXCELLENT = 3;   
    
    always @(Marks)
        if (Marks < 5)
            Grade = FAIL;
        else if ((Marks >= 5) & (Marks < 10))
            Grade = PASS;
endmodule
```

![if_latch](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/if_latch.png)

上面的电路中，当条件 Marks 的值为小于 5 时，电路的输出 Grade 的值为 FAIL，如果 Marks 的值为 5 到 10 之间，那么 Grade 的值为 PASS，由于没有指定 Marks 的值大于 10 的时候 Grade 的值，于是产生的电路中引入了锁存器保存原来 Grade 的值。

由于锁存器和触发器两种时序单元共存的电路会增大测试的难度，因此，在综合的时候尽量只选用一种时序单元，为了不在电路中引入锁存器，可以在使用该语句时设置缺省的状态，即在判断条件之前先对输出赋值，或者使用 if…else if…else 的语句结构。

上面的例子经过改动后可以得到下面的例子——

```
module ComputeNoLatch (Marks, Grade);
    input [1:4] Marks;
    output [0:1] Grade;
    reg [0:1] Grade;
    parameter FAIL = 1, PASS = 2, EXCELLENT = 3;   
    
    always @(Marks)
        if (Marks < 5)
            Grade = FAIL;
        else if ((Marks >= 5) & (Marks < 10))
            Grade = PASS;
        else 
        Grade = EXCELLENT;
endmodule
```
![if_no_latch](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/if_no_latch.png)

#### 2.3 case 语句的综合

##### 2.3.1 条件互斥的 case 语句

对于条件互斥(mutually exclusive)的 case 语句来说，它不存在优先级的概念。先看一个 case 语句的简单实例——

##### 2.3.2 Casex 语句

##### 2.3.3 隐含 Latch 的 case 语句


##### 2.3.4 Full case


##### 2.3.5 Parallel case


##### 2.3.6 case 项不是常数的 case 语句


#### 2.4 loop 语句的综合

#### 2.5 触发器综合

#### 2.6 算术电路的综合

