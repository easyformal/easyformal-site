---
weight: 5
title: "Conformal 快速上手指南"
description: "Conformal 快速上手指南"
---

### 1. 等价性验证流程

![lec_flow](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/5/flow.png)

#### 1.1 Map

Golden 和 Revised 关键点匹配规则：

![map](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/5/map.png)

#### 1.2 Compare

- 只能比较匹配上的关键点。
- 比较是一个迭代过程。
- 可以使用 Control-c 中断比较。输入 compare 以继续比较。

#### 1.3 Debug

查看 Map 和 Compare 结果，并对不等价的比较点进行 Diagnose（诊断）：

![debug](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/5/debug.png)

Compare 结果分类：

- Equivalent 等价：关键点被证明等价（绿色实心圆圈）
- Inverted-Equivalent 反向等价：关键点被证明互补（分开的绿色实心圆圈）
- Non-Equivalent 非等价：关键点被证明不同（红色实心圆圈）
- Abort 中止：由于超时或其他系统参数，关键点尚未被证明等价或非等价（黄色实心圆圈）
- Not-Compared 未比较：关键点尚未比较

### 2. 易于验证的 RTL 设计

#### 2.1 RTL 规则检查器

LEC 的 RTL 规则检查器提供了一种快速简便的方法来检测可能影响验证的 RTL 编码风格。在 RTL 设计过程的早期运行 LEC RTL 规则检查器可以减少以后许多潜在的综合和验证问题。

在 RTL 设计过程的早期运行 LEC RTL 规则检查器可以减少以后许多潜在的综合和验证问题。

示例：

```
SETUP> read design -golden rtl.v
SETUP> read design -revised rtl.v
SETUP> set system mode lec
SETUP> report rule check -golden -design -verbose > lint.rpt
SETUP> report message -golden -model -verbose > model.rpt
```

索引超出范围被报告为：

// Warning: (RTL7.3) Array index in RHS might be out of range (occurrence:1)

注意：当索引超出范围时，将创建 Don't Care。

#### 2.2 Don’t-Care 条件

RTL 出现以下情况会导致产生 Don’t-Care ：

- X 赋值
- 不完整的 case
- 超出范围的索引
- 范围约束 (VHDL)

可以将 Don’t-Care 综合为常量（0或1）。设计中包含大量 Don’t-Care 可能难以验证。

#### 2.3 逻辑结构化

结构相似性： RTL 结构与网表的匹配程度

RTL 和网表之间结构相似性越高的设计越容易验证。

综合可以重构代码。例如：
- 资源共享
- 将无符号运算符映射到有符号运算符

通过以下方式尽量减少 RTL 和网表之间的结构差异：
- 使用 Verilog 2K 编写有符号算术代码
- 使用带括号的显式分组（例如加法）
- 手动编写资源共享代码

#### 2.4 设计分割

将复杂块划分（Partitioning）为更小的部分以便于验证。较小的块更容易验证。划分良好的设计还可以利用更多技术来简化验证。

建议：
- 保持高复杂度设计模块的大小
- 避免逻辑锥深度过大
- 将数据路径块（Datapath）（尤其是需要 retiming 重定时的块）与控制块分开
- 划分可能会影响 Q&R，因此应在设计周期的早期探索权衡


### 3. 可验证的综合流程

**关键：综合流程需要易于验证**

#### 3.1 高级综合技术带来的验证挑战

- Datapath Architecture（数据路径结构）
- Resource Sharing（资源共享）
- Boundary Optimization（边界优化）
- Phase Inversion（相位反转）

考虑验证的综合流程可以显著减少验证挑战

-更轻松地识别综合错误
- 允许使用更多 LEC 功能（例如基于模块的数据路径分析、层次比较 hierarchical compare）来简化验证过程

#### 3.2 Datapath Module 的综合优化

• RC 和 DC 等综合工具可以将多个数据路径运算符分组为单个数据路径模块。这些模块可以是综合出来的，也可以是实例化的组件，例如 DW 模块

• 对于 Design Compiler，这些模块在资源报告中以字符串 DP_OP 作为命名约定

• 如果应用了 ungroup （打平）和 boundary optimization（边界优化），则不会保留这些模块边界，因此很难验证

#### 3.3. 多阶段综合

确保易于验证的基本原则是**将难以验证的综合优化分解为综合流程中的各个阶段**

推荐可验证的综合流程：

1. RTL 到第一个映射网表（中间网表）

+ 启用：数据路径综合
+ 禁用：打平、边界优化、相位反转

2. 映射网表（中间网表）到优化映射（最终网表）

• 启用：打平、增量优化、边界优化

对于 RC 综合工具来说，上述综合流程是默认开启的，而对于 DC 综合工具，需要额外修改综合脚本，添加 Conformal 推荐的 MDP 综合脚本，先综合出一个可验证的中间网表，再增加综合优化得到最终网表。

#### 3.4 收集 DC 综合过程数据

在综合过程中，应收集以下信息以供验证
- Datapath Resource 文件：这是确保可以轻松验证数据路径密集型设计所必需的
- Change Name 文件：这是确保基于名称的映射以便于验证所必需的
- VSDC 文件：此文件包含可帮助指导验证设置的信息
- 综合 log 文件：这可以包含可帮助指导验证设置的信息


### 4. Abort 解决方案

当 Formal 引擎无法在资源限制内提供完整的等效性证明时，将报告 Abort。

#### 4.1 检查综合流程

+ 遵循前面给出的指导原则可以避免中止
+ 对于数据路径密集型设计
- 检查 MDP 综合是否已用于 DC 综合
- 使用 Netlist 验证流程进行 RC 综合
+ RTL 设计以方便验证
- 使用 LEC 的规则检查器和设计报告检查过多的Don’t-Care
+ 对设计进行良好的分层并使用 LEC 的层次比较
- 检查是否可以对所有复杂模块进行层次比较

#### 4.2 检查 LEC Dofile 脚本

+ 层次比较
- 检查是否使用了层次比较
- 对于包含中止的模块，检查它是否没有可以进一步进行层次比较的子模块

+ 对于数据路径密集型设计
- 检查是否已使用 MDP（Analyze datapath -module）
- 检查数据路径分析是否成功

+ Abort分析
- 检查是否使用了 LEC 的 Abort 分析

+ 多线程
- 检查 Abort 分析是否使用了多线程

#### 4.3 LEC 高级技术

有几种高级技术可用于解决 Abort

1. `analyze datapath` 的高级选项
- -wordlevel
- -share
- -effort high
- -addertree

2. 高级命令和技术
- 运行 partition_compare（帮助运行partition_compare -verbose）
- 添加 partition points
- read design -norangeconstraint -vhdl