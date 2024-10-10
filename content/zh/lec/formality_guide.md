---
weight: 4
title: "Formality 快速上手指南"
description: "Formality 快速上手指南"
draft: true

---

### 1. Formality 优势

Formality 可以方便快速地验证自家软件处理的设计，如 Design Compiler 综合前后的等价性验证。

- 支持验证所有 Design Compiler Ultra 默认优化  
- 无需关闭优化即可通过等价性验证  
- 多语言混合编译（Verilog、SystemVerilog 或 VHDL）  
- 低功耗 (UPF) 设计支持  
- Design Compiler Ultra 的自动设置环境，减少手动设置

### 2. Formality 流程

- read：读入 Reference 设计、 Implementation 设计和库文件，将 Ref 和 Imp 设计划分为逻辑锥和比较点。  
- match：映射两个设计之间的相应的比较点。  
- verify：检查每对比较点的逻辑等价性
- debug：使用 GUI 和日志报告。

### 3. 使用 Formality 

#### 3.1 启动 Formality 

- 运行典型的 Formality Tcl 脚本  
` % fm_shell –f runme.fms |tee runme.log `

- 启动 GUI

` % formality ` 或者  
` % fm_shell –gui –f runme.fms |tee runme.log `

- 在批处理会话中启动 GUI

` fm_shell (setup)> start_gui `

- 查看其他调用选项

` % fm_shell -help `

#### 3.2 Formality 生成的文件

- 记录执行过的命令：fm_shell_command.log  
- 日志文件：formality.log  
- 工作文件：FM_WORK 目录、fm_shell_command.lck 和 formality.lck 文件。（当您正常退出工具时，Formality 会自动删除所有工作文件）


### 4. 工作流程

![formality_flow](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/formality_flow.png)

#### 4.1 低功耗验证流程

![low_power_flow](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/low_power_flow.png)


数据要求：

- RTL 和 UPF 必须使用 Synopsys 工具 VCS NLP 进行仿真  
- Design Compiler 网表可以是 verilog 或者 DDC  
- UPF 必须来自 Design Compiler 的 save_upf 命令

- 技术库：电源感知单元必须具有电源引脚和断电功能；Formality 可以为标准逻辑功能单元创建电源引脚

#### 4.2 一个基础脚本
```
#Step 0: 读 Guidance 文件
set_svf default.svf

#Step 1: 读 Reference 设计
read_verilog -r alu.v
set_top alu
load_upf –r alu.upf

#Step 2: 读 Implementation 设计
read_db –i lsi_10k.db
read_verilog -i alu.fast.vg
set_top -auto
load_upf –I alu.fast.upf

#Step 3: Setup
#这里可以进行一些 Setup 设置

#Steps 4 & 5: Match 和 Verify
verify

```

### 5. Guidance

#### 