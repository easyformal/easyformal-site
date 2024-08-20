---
weight: 2
title: "形式验证解决方案：从入门到签核"
description: "形式验证解决方案：从入门到签核"

---
<!--

https://www.systemverilog.io/verification/blueprint-for-formal-verification/

https://blog.csdn.net/Holden_Liu/article/details/124387333


https://singularitykchen.github.io/blog/2021/01/29/Glean-Formal-Signoff/

### 简介

随着集成电路规模的不断扩大，从设计到流片（Tape-out）的全流程中，验证环节的核心地位日益凸显。

对于任何验证方法来说，成功的关键在于制定可靠的策略。为此，这里提供一个形式化验证（Formal）的解决方案。这是一个模板或验证计划，您可以在执行形式化验证时可以借鉴参考。

在本文中我们使用 Synopsys 的 VC Formal 工具。但这里的所有操作也可以使用任何其他 Formal 工具来完成。

该解决方案简单分为 3 个步骤：

- 熟悉工具和 DUT

对形式验证来说，花一些时间来熟悉工具和待测设计（DUT）很重要。

1. 搭建 Formal TestBench

2. 使用 Formal 工具自动检测组合循环、算术溢出和数组超出范围索引等问题

3. 使用 Formal 自动检测无法访问的死代码（unreachable code）

- 属性验证（FPV）

写 SVA （SystemVerilog Assertion） 不是一件容易的事，这里将是耗费大量时间的地方，测试计划在此步骤中创建和实施。

1. 创建 Formal 的测试计划

2. 编写代码约束、断言等

3. 使用抽象来提高证明深度

- 签核（Sign-off）

Sign-off 的最终目的是确保“你所写的内容”确实涵盖了你预期的所有场景。因此，需要考虑以下问题：

是否有足够的属性来检查并覆盖所有的设计？
是否存在由于不正确的约束而导致的无效证明？
该设计是否已经经过足够深度的序列分析？
设计的哪些部分真正得到了验证？
断言可以捕获设计中所有可能的错误吗？

### 步骤1：熟悉工具

我们首先创建一个空的 formal testbench，并通过在 DUT 上运行一些健全性检查并检查是否存在 unreachable 或者 dead code 来熟悉该工具。

#### 1.1 创建 formal testbench

formal testbench  主要由 4 个文件组成

- design.sv – DUT 代码
- fv_design.sv – testbench
- vc.tcl– 工具的运行脚本
- filelist.f– 设计和 testbench 所用的文件列表

假设您的 DUT 是一个仲裁器，其模块端口列表如下

formal testbench 本质上是嵌入在 DUT 中的 Verilog 模块。因此，创建一个 fv_arbiter.sv 如下所示的 formal TB 文件。此文件执行两项操作：

- 它创建了一个名为 的模块fv_arbiter。由于您将从编写输入上的约束和输出上的断言开始，您会注意到此模块具有与 DUT 相同的端口列表，唯一的区别是outputsDUT 的 成为测试台的输入。
- 使用 SystemVerilog 语句将正式测试平台嵌入到 DUT 中bind。

创建 filelist.f 并包含属于该 testbench 的所有文件

-->
