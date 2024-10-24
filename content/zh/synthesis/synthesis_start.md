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

![rtl_code](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/rtl_code.png)

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

![always_code](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/always_code.png)

电路综合后的网表如下所示：

![always](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/always.png)

使用 always 语句描述组合电路要注意的是：在该语句中读入的所有变量都需要出现在事件列表中(对 Verilog 语言而言是指“@”符号之后的信号)，否则可能会得不到用户期望的结
果。

#### 2.2 if 语句的综合

if 语句用于描述受条件控制的电路，下面是一个例子：

![if_code](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/if_code.png)


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

![case_1_code](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/case_1_code.png)

![case_1](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/case_1.png)

从条件互斥的 case 的行为来看，它有点像 if…else if…else 这种结构的 if 语句，也就是
说 case 表达式(Op)先同 case 的第一个 case 项(ADD)，如果不匹配的话再同第二个(SUB)比较，
依次类推。与上例等价的 if 语句如下所示——

![case_2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/case_2.png)

##### 2.3.2 Casex 语句

在 casex 语句中，case 项中的 x 或者 z 的值表示不关心(don’t-care)。从综合的角度看，这些值不能作为 case 表达式的一部分。下面是一个用 casex 语句描述优先级编码器的例子——

![casex](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/casex.png)

上述的 casex 语句所表达的电路与下面的 if 语句一样——

![casex_code](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/casex_code.png)

可见 casex 所描述的电路是具有优先级的。如果我们将上例中的 casex 用 case 语句代替(同时将 case 项中的 x 用 0 代替)，则综合出来的电路将不具有优先级。

##### 2.3.3 隐含 Latch 的 case 语句

与 if 语句类似，如果没有指出 case 项的所有可能情况，则会在电路中引入锁存器（Latch），下面是一个例子——

![case_latch](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/case_latch.png)

上例中的 时，NextToggle 信号没有在所有可能情况下赋值，故在 Toggle=0 或 3 时，NextToggle 保持原有的值，从而产生 Latch。避免产生 latch 的一个方法是给被赋值信号(NextToggle)赋初值。一种方法是加在 case 的最后加入一种 default 的情况（如下）

![case_default1](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/case_default1.png)

或者在 case 语句之前就对被赋值信号加上一个初值（如下）

![case_default2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/case_default2.png)

##### 2.3.4 Full case

从 2.3.3 的例子我们知道，如果条件不全，case 综合之后会产生 latch。如果设计者知道除了列出的一些 case 项之外不会再有其他的条件出现，也就是说 Toggle 的值除了 2'b01 和2'b10 之外不会有其他的值，而且又不想让电路产生 latch，那么他就需要把这种情况告诉综合工具，这里就可以通过一条综合指令(synthesis directive)——synopsys full_case 来传达。综合指令是 HDL 语言中的一类特别的代码，它负责向综合工具传递额外的信息；由于综合指
令是以注释的形式存在于 HDL 代码中的，它对 Verilog 语言本身没有其他影响。

加入综合指令之后，电路如下所示——


![full_case](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/full_case.png)

可见在加入 full_case 综合指令后，综合的结果不存在 Latch。但是要注意的是：
- 加入综合指令会使代码的结果依赖于所用的综合工具，从而降低代码的可移植性。
-  加入综合指令后产生的电路网表会和当初的 Verilog 建模有出入，导致验证的复杂

##### 2.3.5 Parallel case

从 2.3.3 节可以看出，casex 语句是具有优先级的，与 if…else if …else 语句相当。那么假如我们知道 case 项是互斥的该怎么办呢？(在互斥的情况下，case 将平行的检查 case 项中所有可能的情况，而不是先检查第一个然后第二个……)。这时，我们需要将互斥的信息传达给综合工具，这就是 parallel_case 的综合指令。当加上这条指令后，Design Compiler 能够理解 case 项是互斥的，这样就不会产生带优先级的电路，而是平行的译码结构。

加入综合指令后的电路如下所示——

![pallalel_case](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/pallalel_case.png)

与上面的 casex 语句对应的 if 语句如下——

![pallalel_case_code](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/pallalel_case_code.png)

由于 parallel_case 同 full_case 一样都是综合指令语句，在应用 parallel_case 的时候也要考虑到可移植性和提高验证复杂度的问题。


##### 2.3.6 case 项不是常数的 case 语句

前面讨论的 case 项都是常数，实际上我们也会遇到 case 项不是常数的情况，如下例—

![non_const_case](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/non_const_case.png)

这里加入 full_case 指令是相当必要的，否则综合后会引入 latch(Pbus 全不为 1 的情况没
有考虑)。另外，也可以通过赋初值的办法避免 latch 的产生。

值得注意的是，case 项不是常数与 case 项是常数不同，它综合后的电路是带优先级的。

#### 2.4 loop 语句的综合

 Verilog 语法中，一共有四种 loop 语句——while-loop, for-loop, forever-loop 以及 repeat-loop。其中 for-loop 使用的最多，也是一种典型的可以被综合的 loop 语句。For-loop 语句综合的基本原则就是将里面的所有语句进行展开，下面举一个例子——

```
module DMultiplexer (Address, Line);
    inout [1:0] Address;
    output [3:0] Line;
    reg [3:0] Line;

    integer J;

    always @ (Address)
        for (J = 3; J >= 0; J = J - 1)
            if (Address == J)
                Line[J] = 1;
            else 
                Line[J] = 0;
endmodule 
```
![loop](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/loop.png)

将 loop 语句展开之后，可以得到下面的 if 语句——

![loop_code](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/loop_code.png)

使用 loop 语句值得注意的地方是：不要在循环体内加入一些延时或面积较大的单元（例如加法器）。由于 loop 语句综合时需要展开循环体，所以相当于把循环体内的单元复制出来，循环多少次则复制多少次，这样势必会造成综合后的网表面积和延时很大，影响性能。

#### 2.5 触发器综合

触发器是组成时序电路的一个基本元件，也是 Design Compiler 作静态时序分析的要素
之一，当一个信号（变量）在通过 always 语句在时钟边沿（上升沿或下降沿）赋值时，触
发器就可以推断出来。先看下面的一个例子——


![2bit_adder](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/2bit_adder.png)


上面的 always 语句说明，每当 ClockA 出现一次上升延跳变，信号 Counter 就加 1。由于 Counter 是受时钟上升沿控制的，那么它综合以后会出现上升沿的触发器。

描述时序电路要注意一点：如果一个信号既要在 always 内部赋值也要在 always 语句之外赋值，那在 always 内部赋值时需要用非阻塞赋值语句，如上例中的 Counter<=Counter + 1。这样可以准确的反映时序电路的行为。

在读入 Verilog 文件的时候，Design Compiler 能够分析出代码中的时序元件(触发器和锁存器)，并将结果报告出来。

#### 2.6 算术电路的综合

DC 在综合遇到运算符的时候，会在 DesignWare 中选取合适的逻辑电路来实现该运算符。DesignWare 是集成在 DC 综合环境中的可重用电路的集合，主要包括‘＋’‘－’‘×’等算术运算符和‘<’‘>’,‘<=’‘>=’等逻辑运算符。针对同一种运算符，DesignWare 可能提供不同的算法，具体选择那一种是由给定的限制条件决定的。

DesignWare 分为 DesignWare Basic 与 DesignWare Foundation，DesignWare Basic 提供基
本的电路，DesignWare Foundation 提供性能较高的电路结构。

![dw_foundation](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/dw_foundation.png)

从上图的加法器可以看出，DW Foundation 除了具有 Carry Look-Ahead 和 Ripple Carry 两种结构的加法器外，还有另外四种结构，并且速度更快。

如果要 Foundation 的 DesignWare，除了需要有 DesignWare Foundation 的 Licesen 之外还需要在综合的时候设置 synthetic_library。

`set synthetic_library {dw_foundation.sldb}`

`lappend link_library $synthetic_library`

在 verilog 语言中，一个 reg 类型的数据是被解释成无符号数，integer 类型的数据是被解释成二进制补码的有符号数，而且最右边是有符号数的最低位。
进行算术运算时，它也有各个运算符的优先级，运算按照由左至右进行，如下面的式子——

> SUM <= A*B + C*D + E + F + G

它综合出来会是下面的样子：

![datapath](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/datapath.png)

显然这种结构的延时是很大的，我们可以通过交换运算次序和加入括号形成优化的结构

> SUM <= E + F + G + C*D + A*B

> SUM <= (A*B) + ( (C*D) + ( (E + F) + G))

![datapath2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/datapath2.png)

### 3. 使用 Design Compiler 进行综合

#### 3.1 预综合过程

##### 3.1.1  启动  Design Compiler

- shell 环境执行 dc_shell
- shell 环境执行 dc_shell-t（更强大，推荐）
-design_vision（GUI界面）

##### 3.1.2 库文件设置

1. 工艺库（target_library）

工艺库是综合后电路网表要最终映射到的库，读入的 HDL 代码首先由 synopsys 自带的 GTECH 库转换成 Design Compiler 内部交换的格式，然后经过映射到工艺库和优化生成门级网表。工艺库他是由 Foundary 提供的，一般是.db 的格式。这种格式是 DC 认识的一种内部文件格式，不能由文本方式打开。.db 格式可以由文本格式的.lib 转化过来，
他们包含的信息是一致的。下面是一个.lib 的工艺库例子——

![target_library](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/target_library.png)

从图中可以看出，工艺库中包含了各个门级单元的行为、引脚、面积以及时序信息（有的工艺库还有功耗方面的参数），DC 在综合时就是根据 target_library 中给出的单元电路的延迟信息来计算路径的延迟。并根据各个单元延时、面积和驱动能力的不同选择合适的单元来优化电路。

在 tcl 模式下，我们可以根据下面的命令指定工艺库——

> set target_library my_tech.db

2. 链接库（link_library）

link_library 设置模块或者单元电路的引用，对于所有 DC 可能用到的库，我们都需要在 link_library 中指定，其中也包括要用到的 IP。

值得注意的一点是：在 link_library 的设置中必须包含 "\*"， 表示 DC 在引用实例化模块或者单元电路时首先搜索已经调进 DC memory 的模块和单元电路，如果在 link library中不包含 "\*"，DC 就不会使用 DC memory 中已有的模块，因此，会出现无法匹配的模块或单元电路的警告信息(unresolved design reference)。

另外，设置 link_library 的时候要注意设置 search_path，请看下面这个例子——

![link_library](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/link_library.png)

图中设置了 link_library，但是 DC 在 link 的时候却报错，找不到 TOP 中引用的 DECODE 模块，这说明 link_library 默认是在运行 DC 的目录下寻找相关引用。要使上例的 DECODE 能被找到，需要设置 search_path，如下图所示—

![link_library2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/link_library2.png)

3. 符号库（symbol_library）

symbol_library 是 定 义 了 单 元 电 路 显 示 的 Schematic 的 库 。 用 户 如 果 想 启 动
design_analyzer 或 design_vision 来查看、分析电路时需要设置 symbol_library。符号库的后缀是.sdb，加入没有设置，DC 会用默认的符号库取代。

设置符号库的命令是：`set symbol_library`

4. 综合库（synthetic_library）

在初始化 DC 的时候，不需要设置标准的 DesignWare 库 standard.sldb 用于实现Verilog 描述的运算符，对于扩展的 DesignWare，需要在 synthetic_library 中设置，同时需要在 link_library 中设置相应的库以使得在链接的时候 DC 可以搜索到相应运算符的实现。

##### 3.1.3 读入设计文件

![read_design](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/read_design.png)

Design Compiler 支持多种硬件描述的格式，.db、.v、.vhdl等等，读取不同的文件格式可能需要使用不同的 read 命令。

读取源程序的另外一种方式是配合使用 analyze 命令和 elaborate 命令。

当读取完所要综合的模块之后，需要使用 link 命令将存储区中的模块或实体连接起来，如果在使用 link 命令之后，出现 unresolved design reference 的警告信息，需要重新读取该模块，或者在.synopsys_dc.setup 文件中添加 link_library，告诉 DC 到库中去找这些模块，同时还要注意 search_path 中的路径是否指向该模块或单元电路所在的目录。

##### 3.1.4 设计对象

下图是一个 Verilog 描述的设计实例。

![design_object](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/design_object.png)

Verilog 描述的各个模块可以称之为设计(Design)，里面包含时钟(Clock)，他的输入输出称为端口(Port)，模块中的互连线是线网(Net)，内部引用的元件称为引用(Reference)，引用的实例称为单元(Cell)，引用单元的内部端口是管脚(Pin)。

其中值得注意的是 DC 识别 Clock 不是通过 HDL 的书面表达，而是要通过设计者施加一定的约束来区分的，具体内容后续章节会讨论。