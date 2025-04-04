---
weight: 2
title: "Design Compiler 教程"
description: "DesignCompiler 教程"
draft: true
---

### 1. Design Compiler 综合流程

![dc_flow](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/dc_flow.png)

与一般的综合过程相同，使用 DC 做综合也包含转换、优化和映射三个阶段。转换阶段
综合工具将 HDL 语言描述的电路或未映射的电路用工艺独立的 RTL 级的逻辑来实现，对于
Synopsys 的综合工具 DC 来说，就是使用 gtech.db 库中的 RTL 级单元来组成一个中间的网
表。优化与映射是综合工具对已有的中间网表进行分析，去掉其中的冗余单元，并对不满足
限制条件(如 constraints.tcl)的路径进行优化，然后将优化之后的电路映射到由制造商提供的
工艺库上(如 core_slow.db)。

### 2. 预综合过程

#### 2.1  启动  Design Compiler

- shell 环境执行 dc_shell
- shell 环境执行 dc_shell-t（更强大，推荐）
-design_vision（GUI界面）

#### 2.2 库文件设置

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

#### 2.3 读入设计文件

![read_design](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/read_design.png)

Design Compiler 支持多种硬件描述的格式，.db、.v、.vhdl等等，读取不同的文件格式可能需要使用不同的 read 命令。

读取源程序的另外一种方式是配合使用 analyze 命令和 elaborate 命令。

当读取完所要综合的模块之后，需要使用 link 命令将存储区中的模块或实体连接起来，如果在使用 link 命令之后，出现 unresolved design reference 的警告信息，需要重新读取该模块，或者在.synopsys_dc.setup 文件中添加 link_library，告诉 DC 到库中去找这些模块，同时还要注意 search_path 中的路径是否指向该模块或单元电路所在的目录。

#### 2.4 设计对象

下图是一个 Verilog 描述的设计实例。

![design_object](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/design_object.png)

Verilog 描述的各个模块可以称之为设计(Design)，里面包含时钟(Clock)，他的输入输出称为端口(Port)，模块中的互连线是线网(Net)，内部引用的元件称为引用(Reference)，引用的实例称为单元(Cell)，引用单元的内部端口是管脚(Pin)。

如果各个设计对象互相重名怎么办？

![object_rename](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/object_rename.png)

在上图中，一个设计的端口，连线以及内部一个管脚都有一个相同的名字，假如要对名叫”CLK”的线网设置一个为 5 的负载，那应该怎样表示呢？这里，我们需要借助 DCTCL 的一个特殊的数据类型集合（collection）。

> dc_shell-t> set_load 5 [get_nets CLK]

其中的方括号里面表示在所有的线网中搜索名叫 CLK 的线网，将它的负载值设置为 5。get 命令返回对象的集合，如果这个对象没有找到，则返回为空集合。

除了前面的 get_nets 外，还有下面的一些命令可以搜索设计对象，这里列出了 TCL 和 dcshell 两种语法，便于对比——

![find_obj](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/find_obj.png)

### 3.2 施加设计约束

Design Compiler 是一个约束驱动(constrain-driven)的综合工具，它的结果是与设计者施加的约束条件密切相关的。在这一章里，我们主要讨论怎样给电路施加约束条件，这些约束主要包括——时序和面积约束、电路的环境属性、时序和负载在不同模块之间的分配以及时序分析，在本章的最后一节还将讨论 DC Tcl 语言的一些基本语句。

#### 3.2.1 时序和面积

RTL 模块综合示意图：

![rtl_synth_flow](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/rtl_synth_flow.png)

上图是 RTL 模块的综合示意图，可以看出在 RTL 代码仿真通过以后，就开始将它进行综合，综合时需要对他加入约束和设计属性的信息，DC 根据这些约束将 RTL 模块综合成门级网表，然后分析综合出的网表是否满足约束条件，如果不满足就要修改约束条件，甚至重写 RTL 代码。值得注意的是，上面提到的仅仅是 RTL 模块的综合过程，而不是整个芯片的综合，整个芯片是由很多这样的模块组成的，它的综合过程与上图描述的过程有一定的区别，具体我们将在后面的章节中进行讨论。

##### 3.2.1.1 定义面积约束

因为芯片面积直接关系到芯片的成本，面积越大，成本越高，因此，集成电路的设计总是希望面积尽量小，以减小芯片成本。定义面积约束是通过 set_max_area 命令来完成的，比如——

> dc_shell-t>    current_design PRGRM_CNT_TOP
> dc_shell-t>    set_max_area 100

上面的例子给 PRGRM_CNT_TOP 的设计施加了一个最大面积 100 单位的约束。100 的具体单位是由 Foundry 规定的，定义这个单位有三种可能的标准：一种是将一个二输入与非门的大小作为单位 1；第二种是以晶体管的数目规定单位；第三种则是根据实际的面积(平方微米等等)。至于设计者具体用的是哪种单位，可以通过下面的一个小技巧得到——即先综合一个二输入与非门，用 report_area 看他的面积是多少，如果是 1,则是按照第一种标准定义的；如果是 4，则是第二种标准；如果是其他的值，则为第三种标准。

##### 3.2.1.2 同步设计的时序特点和目标

同步时序电路是 DC 综合的前提，因此这里有必要先讨论一下同步时序电路的特点及目标。这里所讨论的同步时序电路的特点是——电路中的信号从一个受时钟控制的寄存器触发，到达另一个受时钟控制的寄存器。而我们要达到的目标是——约束电路中所有的时序路径，这些时序路径可以分为三类：输入到寄存器的路径 、寄存器到寄存器之间的路径以及寄存器到输出的路径。他们分别对应与下图所示的标号为 N、X 和 S 的电路。

![sync_clk](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/sync_clk.png)

假设在上面的电路中，我们要控制触发器 FF2 到 FF3 之间的时序，即 X 电路的延时，那要通过什么方式让 DC 知道呢？显然一个直观的办法就是定义系统的时钟 Clk，如果我们定义好了 Clk 的周期，那么 DC 会自动的尽量保证从 FF2 触发的信号能在一个周期内到达FF3 寄存器。假如周期是 10ns，FF3 触发器的建立时间(setup time)是 1ns，那么留给 X 电路的延时最大只能有10-1=9ns。

##### 3.2.1.3 定义时钟

![clock_define](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/clock_define.png)

在电路综合的过程中，所有时序电路以及组合电路的优化都是以时钟为基准来计算路径延迟的，因此，一般都要在综合的时候指定时钟，作为估计路径延迟的基准。定义时钟的时候我们必须定义它的时钟源(Clock source)，时钟源可以是端口也可以是管脚；另外还必须定义时钟的周期。另外有一些可选项，比如占空比(Duty Cycle)、时钟偏差(Clock Skew)和时钟名字(Clock Name)。定义时钟采用一个语句 create_clock 完成——

`create_clock -period 10 {get_ports Clk}`   
`set_dont_touch_network {get_clocks Clk}`

第一句定义了一个周期为 10ns 的时钟①，它的时钟源是一个称为 Clk 的端口。

第二句对所有定义的时钟网络设置为 don’t_touch，即综合的时候不对 Clk 信号优化。如果不加这句，DC 会根据 Clk 的负载自动对他产生 Buffer，而在实际的电路设计中，时钟树(Clock Tree)的综合有自己特别的方法，它需要考虑到实际布线后的物理信息，所以 DC 不需要在这里对它进行处理，就算处理了也不会符合要求。

![clock_defined](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/clock_defined.png)

可以看到，定义了系统时钟后，图 44 中的 X 电路已经被约束起来了，但是电路的输入输出两块还没有施加约束，这可以通过 DC 的另外两个命令来完成。

##### 3.2.1.4 约束输入路径

![input_dp_delay](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/input_dp_delay.png)

从上图可以看出，我们所要定义的输入延时是指被综合模块外的寄存器触发的信号在到达被综合模块之前经过的延时，在上图中就是外围触发器的clk-q的延时加上M电路的延时。当确定这段延时之后，被综合模块内部的电路延时的范围也可以确定下来了。加入时钟周期是 20ns，输入延时是 4ns，内部触发器的建立时间为 1.0ns，那么就可以推断出要使电路正常工作，N 电路的延时最大不能超过 20-4-1.0=15.0ns。

设置输入延时是通过 DC 的 set_input_delay 命令完成的

`set_input_delay -max 4 -clock Clk [get_ports A]`

如上面的语句指出了被综合模块的端口 A 的最大输入延时为 4ns。-max 选项是指明目前设置的是输入的最大延迟，为了满足时序单元建立时间（setup time）的要求。另外还有一个选项是-min，它是针对保持时间的约束使用的，后面章节有详细介绍。-clk 是指出这个端口受哪个时钟周期的约束。

定义了输入延时之后，相对应的还要设置电路的输出延时。

##### 3.2.1.5 约束输出路径


![output_dp_delay](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/synthesis/image/1/output_dp_delay.png)

上图中，信号在被综合模块的触发器 U3 里触发，被外围的一个触发器接收。对外围电路而言，它有一个 T 电路延时和外围触发器的建立时间。当确定了他们的延时之后，被综合模块内部的输出路径延时范围也就确定下来了。假如，时钟周期 20ns，输出延时 5.4ns，U3 触发器的 clk-q 延时为 1.0ns，那么输入路径 S 的最大延时就是 20-5.4-1.0=13.6ns。

设置输入延时是通过 DC 的 set_output_delay 命令完成的

`set_output_delay -max 5.4 -clock Clk [get_ports B]`

上面的语句指出了被综合模块的输出端口 B 的最大输出延时为 5.4ns。-max 选项是指明目前设置的是输入的最大延迟；-clk 是指出这个端口受哪个时钟周期的约束。

至此，模块的面积、时钟、输入输出延时都施加了相应的约束。在施加了这些约束之后，可以使用下面的几个命令检查约束是否施加成功

- report_port –verbose 报告在当前设计中所有的输入输出端口属性和施加的约束值
- report_clock 报告当前设计中定义的时钟及其属性情况
- reset_design 删除当前设计中所有的属性值和约束(通常用在约束脚本的第一句) 
- list_libs 列出内存中所有可用的库

#### 3.2.2 环境属性

##### 3.2.2.1 设置输出负载

##### 3.2.2.2 设置输出驱动

##### 3.2.2.3 设置工作条件


##### 3.2.2.4 设置连线负载模型

#### 3.2.3 时序和负载预算

##### 3.2.3.1 时序预算

##### 3.2.3.2 负载预算

#### 3.2.4 时序分析

##### 3.2.4.1 分解时序路径

##### 3.2.4.2 计算单个路径的延时

##### 3.2.4.3 计算整条路径的延时

##### 3.2.4.4 用 report_timing 检查时序

#### 3.2.5 DC 的 Tcl 语法

#### 3.2.6 高级时钟约束

#### 3.2.6.1 非理想的单时钟系统

#### 3.2.6.2 同步多时钟网络

#### 3.2.6.3 异步多时钟网络

#### 3.2.6.4 多周期路径


### 3.3 设计综合过程

### 3.4 后综合过程

