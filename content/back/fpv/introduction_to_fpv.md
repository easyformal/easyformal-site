---
weight: 3
title: "FPV 入门"
description: ""
draft: true

---

### 1. FPV 介绍

FPV 用于通过证明属性（property）来验证 DUT。这些属性可以由用户创建，也可以由商业 AIP 为接口协议或功能块提供。FPV 工具使用数学求解引擎来彻底证明或反驳属性。如果断言失败，FPV 工具将生成反例来演示失败轨迹。

但是，在某些情况下，可能无法明确证明或反驳某个属性。在这些情况下，FPV 将提供有界证明结果，表明从初始状态到特定深度都找不到反例。一组断言的证明结果意味着，在给定的约束下，属性不可能为假。

FPV 工具需要几个输入，包括：

- Verilog/SystemVerilog/VHDL 格式的 RTL 设计文件。
- 写在 SVA 文件中的 assert、assume 和 cover 属性，或 SystemVerilog 设计文件中的 inline SVA。
- TCL 文件，指导工具执行。

然后，FPV 工具将输出属性的状态，例如 assertion 状态、assumption 状态和 cover 状态。断言状态可以是 proven, falsified, vacuous, witness-coverable, uncoverable, or inconclusive。

### 2. FPV 一般流程

- 读设计和属性
- elaborate 设计
- 指定 clock 和 reset
- 应用约束（如有）
- 证明属性
- 交互式 debug（图形界面）

### 3. 考虑 FPV 的局限性

- 随着设计规模的增长，状态空间呈指数增长。机器无法处理设计规模，或者探索状态空间所需的时间无法接受。这称为状态空间爆炸问题。
- FPV 不适用于数据路径函数，除了简单函数。对于算法块尤其如此。
- FA 只能处理 RTL 逻辑，任何模拟模块都将被设置黑盒或被移除。

### 4. VC Formal FPV 参考脚本

```
# 选择 FPV 模式
set_fml_appmode FPV

# 设置顶层模块名称
set design TOP

# 读设计，“+define+INLINE_SVA”允许我们写 SVA 属性在 .sv 文件里面
read_file -top $design -format sverilog -sva \
  -vcs {../design/fpv_example.sv +define+INLINE_SVA}

# 创建 clock 和 reset
create_clock clk -period 100
create_reset rst -sense high

# 运行 reset 模拟
sim_run -stable
sim_save_reset
```



