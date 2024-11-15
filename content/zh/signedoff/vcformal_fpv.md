---
weight: 3
title: "VC Formal FPV 教程"
description: "Synopsys VC Formal Tutorial Formal Property Verification App (FPV)"
draft: true
---

### 1. FPV 介绍

FPV 应用程序用于通过证明属性来验证 DUT。这些属性可以由用户创建，也可以由接口协议或功能块的商业 AIP 提供。该应用程序使用一系列强大的 VC Formal 引擎来彻底证明或反驳属性。如果断言失败，FPV 应用程序将生成反例来展示违规的痕迹。但是，在某些情况下，可能无法明确地证明或反驳某个属性。在这些情况下，应用程序将提供有界的证明结果，表明从初始状态到一定深度都找不到伪造。一组断言的证明结果意味着，在给定的约束条件下，该属性不可能为假的。

![fpv_app](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/signedoff/image/3/fpv_app.png)


FPV 应用程序需要几个输入，包括：

- Verilog/SystemVerilog/VHDL 格式的 RTL 设计文件
- 写在 SVA 文件中的断言、假设和覆盖属性，或写在 SystemVerilog 设计文件中的内联 SVA。
- TCL 文件

然后，FPV 应用程序将输出属性的状态，例如  assertion 状态、assumption 状态和cover 状态。断言状态可以是 proven, falsified, vacuous, witness-coverable, uncoverable, or inconclusive。

### 2. TCL 脚本示例

![fpv_tcl](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/signedoff/image/3/fpv_tcl.png)

### 3. 编写断言

可以使用 INLINE_SVA 将断言写在代码中。

![fpv_code](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/signedoff/image/3/fpv_code.png)

### 4. 运行 FPV

`vcf -gui` 或 `vcf -f run.tcl -gui` 或 `vcf -f run.tcl -verdi`

### 