---
weight: 1
title: "自动提取属性（AEP）入门"
description: ""
---
<!--

### 1. AEP 介绍

当 RTL 设计人员编写了足够多的 RTL 时，应当立即用 AEP 进行基本的验证，而不是等到测试平台可用，再交给验证人员。
因为即使是验证专家，编写断言也是一项非常耗时的任务。

AEP 工具可以根据 RTL 自动生成断言属性检查设计，在 RTL 开发早期就可以让设计人员同步进行检查，
它有助于消除常见的功能设计错误，并确保在验证开始之前代码是干净的，从而提高设计质量并缩短总体时间表。

常用的 AEP 工具有 Synopsys 公司的 VC Formal AEP APP 和 Cadence 公司的 Jasper Superlint App。

### 2. AEP 脚本示例（VC Formal）

```
set_fml_appmode AEP
set_fml_var fml_aep_unique_name true
read_file -top TOP -format sverilog -aep all -vcs {../design/top.sv}
create_clock clk -period 100
create_reset rst -sense high
sim_run -stable
sim_save_reset
```
-->
