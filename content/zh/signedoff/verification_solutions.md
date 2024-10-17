---
weight: 2
title: "形式验证解决方案：从开始到签核（持续更新）"
description: "形式验证解决方案：从开始到签核"

---
### 简介

随着集成电路规模的不断扩大，从设计到流片（Tape-out）的全流程中，验证环节的核心地位日益凸显。在验证领域中，形式验证（Formal） 使用率处于历史最高水平。对于任何验证方法来说，成功的关键在于制定可靠的策略。如果没有彻底的验证解决方案，仍然可能会错过错误！为此，这里提供一个 Formal 的解决方案。这是一个模板或验证计划，你可以在执行 Formal 验证时可以借鉴参考。

在本文中我们使用 Synopsys 的 VC Formal 工具，但也可以用同类其他工具替代。

参考项目：**[Formal-Verification-of-an-AHB2APB-Bridge](https://github.com/easyformal/Formal-Verification-of-an-AHB2APB-Bridge)**

该解决方案简单分为 3 个步骤：

- 熟悉工具和待测设计（DUT）
- 属性验证（Formal Property Verification，FPV）
- Sign-off

### 步骤1：熟悉工具和 DUT

对形式验证来说，花一些时间来熟悉工具和 DUT 很重要。我们首先创建一个空的 Formal Testbench，并通过在 DUT 上运行一些完全自动化的检查（如 AEP、FXP、FCA）来熟悉该工具和探索 DUT。

#### 1.1 搭建 Formal Testbench

通常形式测试台由四个文件组成：

- design.sv – DUT 代码
- design_sva.sv – testbench 代码
- vc.tcl– 运行脚本，指导工具执行任务。
- filelist.f– 列出所有设计和 testbench 文件，以便正确编译。

假设你的设计是一个 AHB2APB 桥接器，其模块端口列表如下

```
module Bridge_Top(Hclk,Hresetn,Hwrite,Hreadyin,Hreadyout,Hwdata,Haddr,Htrans,Prdata,Penable,Pwrite,Pselx,Paddr,Pwdata,Hreadyout,Hresp,Hrdata);

input Hclk,Hresetn,Hwrite,Hreadyin;
input [31:0] Hwdata,Haddr,Prdata;
input[1:0] Htrans;
output Penable,Pwrite,Hreadyout;
output [1:0] Hresp; 
output [2:0] Pselx;
output [31:0] Paddr,Pwdata;
output [31:0] Hrdata;

...

endmodule
```

Formal Testbench 本质上是嵌入在 DUT 中的 Verilog 模块。因此，创建一个 bridge_top_sva.sv 如下所示的 TB 文件。此文件执行两项操作：

- 创建一个 Bridge_Top_sva 模块，assertion、assumption 和 cover 属性将在这里编写。此模块具有与 DUT 相同的端口列表，但是 DUT 的 output 端口成为该 TB 模块的 input 端口。
- 使用 SystemVerilog 的 bind 语句将 testbench 嵌入到 DUT 中。

```
module Bridge_Top_sva(
input logic Hclk,
input logic Hresetn,
input logic Hwrite,
input logic Hreadyin,
input logic [31:0] Hwdata,
input logic [31:0] Haddr,
input logic [1:0] Htrans,
input logic [31:0] Prdata,
input logic [2:0] Pselx,
input logic [31:0] Paddr,
input logic [31:0] Pwdata,
input logic Penable,
input logic Pwrite,
input logic Hreadyout,
input logic [1:0] Hresp,
input logic [31:0] Hrdata);

...

endmodule  

bind Bridge_Top Bridge_Top_sva chk_bridge_top (.Hclk(Hclk), .Hresetn(Hresetn), .Hwrite(Hwrite), .Hreadyin(Hreadyin), .Hwdata(Hwdata), .Haddr(Haddr), .Htrans(Htrans), .Prdata(Prdata), .Pselx(Pselx), .Paddr(Paddr), .Pwdata(Pwdata), .Penable(Penable), .Pwrite(Pwrite), .Hreadyout(Hreadyout), .Hresp(Hresp), .Hrdata(Hrdata));

```

#### 1.2 使用 AEP 进行健全性检查

AEP（自动提取属性） 是 VC Formal 工具中的一个功能模块。AEP 可以自动对超出范围的数组、算术溢出、X 赋值、同时 set/reset、full case、parallel case、多驱动器/冲突总线和浮动总线等检查进行功能分析。

此时，我们的 Formal TB 只是一个空壳，尚未编写任何约束或断言检查器。接下来，我们将运行 AEP 应用程序并对设计执行健全性检查。以下是参考运行脚本

```
# Select AEP as the VC Formal App mode
set_fml_appmode AEP
set design Bridge_Top

set_fml_var fml_aep_unique_name true
read_file -top $design -format sverilog -sva \
-aep all -vcs {-f ../RTL/filelist +define+INLINE_SVA}

# Creating clock and reset signals
create_clock Hclk -period 100 
create_reset Hresetn -sense low

# Runing a reset simulation
sim_run -stable 
sim_save_reset
```

#### 1.3 使用 FXP 检查 X 传播

FXP 应用可以检查设计中未知信号值 (X) 的传播，并允许在 Verdi 原理图和波形中将故障属性追踪到 X 的源。

#### 1.4 使用 FCA 分析覆盖率

覆盖率分析是验证过程中的一个重要步骤，它可以帮助你识别那些在设计中永远不会被执行到的代码部分。这些代码可能是冗余的，或者是由于设计变更而不再需要的。识别并移除这些代码可以提高设计的性能和可维护性。在这里，我们使用 FCA 进行覆盖率分析

FCA 应用专门用于收集覆盖率信息。在这个步骤中，你将使用它来收集“行+条件”（line+cond）覆盖率。这种覆盖率信息将帮助你完成以下两个任务：

- 分析覆盖率报告，找到不可达代码：通过查看覆盖率报告，你可以确定哪些代码行或条件从未被执行过，这些可能就是死代码。
- 创建覆盖率排除列表：基于覆盖率报告，你可以创建一个列表，明确指出哪些代码是故意不被覆盖的，这有助于建立一个基线，明确哪些代码是预期之外的。

### 步骤2：FPV

在进入 FPV 之前，你已经创建了 formal testbench 的基本框架，并对 DUT 进行了基本的错误检查。这包括使用自动提取属性（AEP）应用进行合理性检查，使用 FXP 检查 X 传播，以及使用覆盖率分析器（FCA）应用来识别死代码。现在，你已经准备好进行FPV，这一步骤将占据你大部分的验证工作。写 SVA （SystemVerilog Assertion） 不是一件容易的事，这里将是耗费大量时间的地方，测试计划在此步骤中创建和实施。

#### 2.1 创建测试计划

- 仔细阅读设计规范，基于设计要求创建一个全面的测试计划。
- 明确定义输出的预期行为、不应发生的事件以及输入的预期协议。

测试计划中的每项测试项目都应该用简单、清晰的语言描述，因为这些测试项目中的每一个稍后都将转换为断言，这些断言将用于验证设计是否符合预期行为。

可以参考项目 [Formal-Verification-of-an-AHB2APB-Bridge](https://github.com/easyformal/Formal-Verification-of-an-AHB2APB-Bridge)  中的测试计划。

#### 2.2 编写约束、检查器和 witnesses

- 根据测试计划，编写约束（constraints）来定义输入条件。
- 编写检查器（checkers）来断言输出或内部状态的属性。
- 编写 witnesses 来覆盖特定的行为或条件。

此步骤是验证工作的主要部分。可以从在 output 上写一些简单的输出 cover 属性开始。通过 FPV 应用程序运行这些 cover 属性将产生波形。查看这些波形可以知道该工具和设计基本上符合规格。还可以从测试计划中编写一些简单的检查器。

例如，如果设计规范规定 ack 信号应该在 req 信号发出后正好 2 个时钟周期被置位，您可以编写一个 assertion，如下所示。

```
// Checker example
property req_ack_protocol;
    @(posedge clk) disable iff (rst)
    (req |-> ##2 ack);
endproperty
req_ack_protocol_A: assert property (req_ack_protocol);

// Cover or witness example 
property out_data_witness;
    @(posedge clk) disable iff (rst)
    (out_vld && out_data == 8’haa);
endproperty
out_data_witness_W: cover property (out_data_witness);
```

使用 FPV 应用证明属性，以下是 VC Formal FPV 运行脚本示例：

```
# Select AEP as the VC Formal App mode
set_fml_appmode FPV
set design Bridge_Top

set_fml_var fml_aep_unique_name true
read_file -top $design -format sverilog -sva -aep all -vcs {-f ../RTL/filelist +define+INLINE_SVA ../sva/bridge_top_sva.sv}
#read_waiver_file -elfiles aep.el

# Creating clock and reset signals
create_clock Hclk -period 100 
create_reset Hresetn -sense low

# Runing a reset simulation
sim_run -stable 
sim_save_reset
```


#### 2.3 提高证明深度

### 步骤3：Sign-off

Sign-off 对半导体开发来说，是至关重要的。它是一项强大的技术，但你必须记住，结果的好坏取决于所分析的属性。formal 是完备的，但只针对你编写的内容！因此，formal Sign-off 侧重于确保属性的数量和质量足够，并提供可量化的功能验证完整性衡量标准。Sign-off 的最终目的是确保“你所写的内容”确实涵盖了你预期的所有场景。采取以下七个步骤，以实现 formal Sign-off 的必要信心。

#### 3.1 审查测试计划和规范

第一步是彻底审查测试计划和规范。设计和验证工程师根据测试计划中确定的设计特征编写属性。如果计划不能准确反映规范中的预期功能，则属性可能不完整。

此审查通常由验证团队执行，但设计工程师也可能参与。

#### 3.2 回顾属性和 formal 验证结果

第二步需要设计工程师。他们了解自己的 RTL 代码和预期行为，因此对设计的哪些方面应该通过断言进行检查并在验证过程中进行覆盖有深刻的见解。

#### 3.3 属性结构影响锥分析 (COI)

关注问题：是否有足够的属性来检查并覆盖所有设计？

VC Formal 可以自动执行快速分析，从每个断言或覆盖属性向后追溯，以查看设计的哪些部分在其影响锥 (COI) 内。

此阶段的关键值是识别任何不在任何断言的 COI 内的寄存器、输入或输出，这意味着它们根本没有通过形式分析进行验证。

#### 3.4 过约束可达性分析

关注问题：是否存在由于不正确的约束而导致的无效证明？

过度约束可能掩盖设计错误的问题。如果约束不正确，则形式化分析可能不会考虑某些合法的设计行为。如果此行为涉及触发可以通过断言捕获的错误，则将错过该错误，并且断言的证明无效。

VC Formal 执行过度约束分析以查找由于约束而无法访问的代码。分析会准确报告哪些约束影响设计的哪些部分，显示无法访问的根本原因，并使用户更容易执行必要的调整。

#### 3.5 有限深度分析

关注问题：该设计是否已经经过足够深度的序列分析？

对于具有复杂属性的大型设计，获得每个断言的完整（无界）证明的代价相当高，因此有限深度分析非常重要，必须重新审视这一步并确认达到的深度是否足够。

VC Formal 应用可以生成有界证明的算法并报告每个此类证明的循环数（深度）。它还提供有关整体设计的顺序深度的信息，以帮助用户确定所实现的有界证明是否提供了高度的信心（尽管不是确定性），即设计是正确的。

#### 3.6 形式化生成的属性驱动逻辑核心（Formal Core）

关注问题：设计的哪些部分真正得到了验证？

COI 方法速度很快，但在判断断言密度和质量时过于乐观。COI 中的某些寄存器或输入可能实际上不参与相关断言的证明（完整或有界）

VC Formal 对每个 COI 的子集执行 Formal Core 分析，以确定证明需要哪些寄存器或输入。

#### 3.7 自动故障注入断言压力测试 (FTA)

关注问题：断言可以捕获设计中所有可能的错误吗？

Formal Core 分析比 COI 更精确，但它无法回答 Formal 收尾的最终问题。它可以告诉用户某个寄存器的某些部分已经检查过，但不能告诉用户是否所有部分都已检查过。

最后一步将 VC Formal 与 Synopsys Formal Testbench Analyzer (FTA) 应用程序相结合，以提供最精确的断言指标。FTA 应用程序使用 Synopsys Certitude 功能鉴定系统将故障（突变）插入设计中，以模拟通常在 RTL 代码中发现的错误类型。

它在存在人为插入的故障的情况下分析属性的结果。如果在存在故障的情况下至少一个属性失败，则断言是好的，如果没有失败，则表明存在验证漏洞。
