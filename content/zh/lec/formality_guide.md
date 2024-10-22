---
weight: 4
title: "Formality 快速上手指南"
description: "Formality 快速上手指南"
---
### 1. Formality 优势

Formality 可以快速验证自家工具的流程，配合 Design Compiler 和 IC Compiler 对综合前后和 PR 前后进行等价性验证。优点：对自家工具，开箱即用！

- 支持验证所有 Design Compiler Ultra 默认优化
- 无需关闭优化即可通过等价性验证
- 多语言混合编译（Verilog、SystemVerilog 或 VHDL）
- 低功耗 (UPF) 设计支持
- Design Compiler Ultra 的自动设置环境，减少手动设置

### 2. Formality 流程概括

- read：读入 Reference 设计、 Implementation 设计和库文件，将 Ref 和 Imp 设计划分为逻辑锥和比较点。
- match：映射两个设计之间的相应的比较点。
- verify：检查每对比较点的逻辑等价性
- debug：使用 GUI 和日志报告。

### 3. 使用 Formality

#### 3.1 启动 Formality

- 运行典型的 Formality Tcl 脚本 `% fm_shell –f runme.fms |tee runme.log`
- 启动 GUI

`% formality` 或者 `% fm_shell –gui –f runme.fms |tee runme.log`

- 在批处理会话中启动 GUI

`fm_shell (setup)> start_gui`

- 查看其他调用选项

`% fm_shell -help`

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

#### 5.1 什么是 Guidance

SVF 是 Formality 使用的自动 Guidance 设置文件，它由 Design Compile 在综合时自动生成并传递到 Formality。

- 建议使用 SVF 流程
- 验证包含 retiming、register merging（寄存器合并）、register inversions（寄存器反转）时必需
- 包含 setup 和 guidance 信息
- 减少用户 setup 的工作量和错误
- 消除不必要的验证迭代
- SVF 数据在 Formality 中隐式或显式证明或者不被使用

  SVF 不是明文格式的，不能被 Formality 外的验证工具使用。如果想用第三方的 Formal 工具验证 DC 综合的设计，可以使用明文的 VSDC 文件，VSDC 文件通过 DC 的 set_vsdc 命令生成，但它仅包含部分基础的 guidance 信息，也可以用 SVF 读入 Formality 后自动解析生成的明文 svf.txt 文件，它会包含所有的 setup 和 guidance 信息。

#### 5.2 Guidance 文件的内容

SVF 包含以下信息：

- 对象名称变化 *guide_change_names*
- 常量寄存器优化 *guide_reg_constant*
- 复制和合并寄存器 *guide_reg_duplication*、*guide_reg_merging*
- 乘法器和除法器架构类型 *guide_multiplier*
- 数据路径转换 *guide_datapath*
- FMS 重编码 *guide_fsm_reencoding*
- 重定时  *guide_retiming*
- 寄存器相位反转 *guide_inv_push*
- 分组和取消分组 *guide_group*、*guide_ungroup*
- 唯一化和取消唯一化 *guide_uniquify*、*guide_ununiquify*

#### 5.3 使用自动 Setup 模式

通过设置变量 `set synopsys_auto_setup true` 使用自动 setup 模式（在 set_svf 命令之前）

- 在 Design Compiler 中做出的 assume 在 Formality 中也同样适用  
- 提高开箱即用验证成功率
- 有无 SVF 均可使用，使用 SVF 可实现更多功能
- 处理 undriven 信号与综合时保持一致
- RTL 的解释和编译与综合时保持一致
- 自动启用 clock-gating 和 自动禁用 scan（需要 SVF）

#### 5.4 自动 Setup 的优势

- 更容易使用 Formaltiy
- 减少调试成本
- 大部分验证失败都是 setup 不正确或者缺失导致的假失败
- 大幅减少手动设置
- 简化整体验证工程

### 6. Read 

#### 6.1 Read 相关命令

Formality 输入格式：

- Verilog  -read_verilog  
- VHDL  -read_vhdl  
- SystemVerilog  -read_sverilog  
- Synopsys Milkyway -read_milkyway  
- Synopsys 二进制文件 -read_db, read_ddc  
- UPF 文件 -load_upf  

指定读入容器

- -r  默认 reference 容器（Golden）
- -i  默认 implementation 容器（Revised）

**用仿真风格读 verilog**，read_verilog 支持 VCS 风格。如 read_verilog -r top.v -vcs "option"，其中 "option" 包括：
- -y <directory_name>：在 <directory_name> 中搜索未解析的模块。
- -v <file_name>：在 <file_name> 中搜索未解析的模块。
- +libext+<扩展名>：查看具有此扩展名的文件，通常为“.v”或“.h”。
- +define+：定义 Verilog 参数的值。
- +incdir <dirname>：包含 include 文件的目录。
- -f <file_name>： VCS 选项文件。


#### 6.2 Low Power 数据加载

Formality 会修改 reference 或 implementation 设计以满足 UPF 命令所隐含的规范，UPF 的命令不会以交互的方式发出。

以下是一个验证 RTL+UPF 和 DC 综合网表+UPF 的脚本示例,：

```
read_db {low_power_library.db special_lp_cells.db}
read_verilog –r {top.v block1.v block2.v block3.v}
set_top r:/WORK/top
load_upf –r top.upf
read_verilog –i {post_dc_netlist.v} set_top i:/WORK/top
load_upf –i top_post_dc.upf
```

### 7. Setup

#### 7.1 验证所需的 Setup

- match 和 verify 可能需要 guidance，特别是对于 retiming、寄存器合并、寄存器相位反转，需要用自动 setup 文件，如 SVF。
- 需要注意的 design 转换设置
    - 内部扫描 Internal Scan
    - 边界扫描 Boundary Scan
    - 时钟门控 Clock-gating
    - 时钟树缓冲 Clock Tree Buffering
    - 有限状态机重编码 FSM Re-encoding
    - 黑盒 Black boxes
- 自动 setup 模式 7.2 

#### 7.2 Internal Scan

**什么是 internal scan**

internal scan 是由 DFT Compiler 实现的，扫描链使设置和观察 design 内部寄存器的状态变得更加容易，以便进行测试。

- 用 scan 触发器 替换触发器
- 将 scan 触发器连接到 shift register（移位寄存器）或扫描链

**为什么要注意 internal scan**

扫描插入期间添加的附加逻辑会改变组合功能

![internal_scan](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/internal_scan.png)

**怎么处理 internal scan**

- 确定哪些端口可以 disable 扫描电路（DFT Compiler 的默认是 test_se）
- 使用 set_constant 命令将这些端口设置为非活动状态

```
fm_shell (setup) > set_constant i:/WORK/TOP/test_se 0
```
#### 7.3 Boundary Scan

**为什么要注意 boundary scan**

- 主输出处 po 的逻辑锥不同。
- 主输入 pi 驱动的逻辑锥不同。
- design 具有额外的状态控制元件。

![boundary_scan](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/boundary_scan.png)

**怎样处理 boundary scan**

禁用边界扫描：
- 如果设计具有可选的异步 TAP 复位引脚（例如 TRSTZ 或 TRSTN），则使用
set_constant 在该引脚上禁用扫描单元。
- 如果设计只有 4 个强制 TAP 输入（TMS、TCK、TDI 和 TDO），则使用 set_constant 命令强制 design 的内部 net 。

#### 7.4 Clock-gating

**什么是 clock gating**

clock gating 由 Power Compiler 添加
- 在寄存器的时钟路径中添加逻辑，当寄存器输出不变时禁用时钟
- 通过不对寄存器单元进行不必要的时钟控制来节省电量

![clock_gating](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/clock_gating.png)

**clock gating 会有什么问题**

如果不进行干预，比较点将无法通过验证。

- 每个时钟门控 latch 都会成为一个比较点，但该比较点在对比 design 中没有，因此会导致 match fail。
- 寄存器组 register bank 的时钟输入逻辑已被修改，register bank 比较点会 verify fail。


**如何处理 clock gating**

-`set verification_clock_gate_hold_mode low`

如果时钟门控 clock-gating net 驱动的是正沿（positive edge ）触发的 DFF 时钟引脚，请使用 low 或 any 选项。

如果 clock-gating net  还驱动主输出（PO）或黑盒输入，请使用
collapse_all_cg_cells 。

如果 clock-gating cells  不驱动 DFF 的任何时钟引脚，则使用 set_clock 命令来识别 PI 的 clock net。

- 自动  setup 模式默认启用时钟门控

- 仅当时钟门控验证问题继续存在时才使用以下变量：

`set validation_clock_gate_edge_analysis true`

#### 7.5  Clock Tree Buffering

时钟树缓冲是在时钟路径中添加缓冲器 buffer 以允许时钟信号驱动大负载。


![clock_tree_buffer](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/clock_tree_buffer.png)

**如何处理时钟树缓冲**

- 在验证 top module 时，无需任何处理
- 层次化验证（Hierarchical Verification）在验证一个子模块时，使用 `set_user_match` 命令来声明时钟引脚是等效的

```
fm_shell (setup)> set_reference_design r:/WORK/blocka
fm_shell (setup)> set_implementation_design i:/WORK/blocka
fm_shell (setup)> set_user_match r:/WORK/blocka/clk \
i:/WORK/blocka/clk1 \
i:/WORK/blocka/clk2 \
i:/WORK/blocka/clk3
fm_shell (setup)> verify
```

#### 7.6 FSM 重编码

SVF 文件中包含 FSM 重编码信息，Formality 自动 setup 模式默认启用该信息。

可以通过查看 ./formality_svf/svf.txt,验证 FSM 重编码是否正确。

`set svf_ignore_unqualified_fsm_information false`

#### 7.7 黑盒

黑盒是不包含任何逻辑的模块或实例。

不需要验证的模块：模拟电路、存储设备。

reference design 和 implementation design 两边的黑盒需要匹配。

### 8. Match

#### 8.1 匹配比较点

match 做的第一件事是验证并应用 guidance（如果已设置 SVF），使用 SVF 流程可提高名称匹配性能和完成度。

匹配时首先根据名称匹配，然后通过签名分析（逻辑椎结构技术）来匹配剩余比较点。

用户可以指定比较规则或手动设置匹配。

set_user_match 可以声明匹配两个比较点。

#### 8.2 命名规则

当名称以可预测的方式发生变化时，编写比较规则。使用 SED 语法将一个 design 中的名称转换为另一个 design 中的相应名称：

```
fm_shell (match)> set_compare_rule $ref \
–from {i_tv80_core} -to {}
fm_shell (match)> match
```

### 9.  verify

#### 9.1 验证设计

Formality 部署了许多不同的的求解器，在每对比较点上运行验证算法。如果每对比较点的逻辑椎功能相同，则该点 passe，反之则是 failed。验证有四种可能的结果：

- Succeeded: Implementation 设计等价于 Reference 设计。
- Failed: Implementation 与 Reference 设计不等价。
- Inconclusive: （不确定），没有点失败，但分析不完整可能是由于超时或复杂性。
- Not run:: 流程早期的问题阻止了验证的运行。

#### 9.2 控制验证运行时间

- `set verification_timeout_limit hrs:min:sec`: 设置验证时间限制，超时会停止验证，默认限制为 36 CPU 小时。（0:0:0 表示无超时）

- `set verification_failing_point_limit number`: 在指定数量的比较点失败后停止验证（默认为 20 个失败比较点），然后可以开始纠错和调试。

- `set verification_effort_level [super_low | low | medium | high]`:  指定解决比较点所花费的工作量（默认值为高），使用 super_low 可以快速找到失败的比较点，但也会产生多个中止的比较点。

#### 9.3 Hierarchical Verification

使用命令 `write_hierarchical_verification_script` 可以生成 tcl 脚本，对当前 reference 设计和 implementation 设计执行分层验证，有助于调试大型且难以验证的设计。用法：

```
set_top i:/WORK/top set_constant $impl/test_se 0
write_hier –replace –level 3 myhierscript
source myhierscript.tcl
quit
```

#### 9.4 多核支持

- 单个 license 最多支持制定 4 个内核。
- 单个设置命令： `set_host_options -max_cores num_cores `
- 报告最大内核数：`report_host_options`

### 10. Debug

#### 10.1 Formality 典型的脚本示例

```
set search_path “. ./rtl ./lib ./netlist”
set synopsys_auto_setup true
set hdlin_dwroot /tools/syn/E-2010.12
set_svf default.svf
read_verilog -r "fifo.v gray_counter.v \
        pop_ctrl.v push_ctrl.v rs_flop.v"
set_top fifo
read_db –i tcb013ghpwc.db
read_verilog -i fifo.vg
set_top fifo
# set_constant $impl/test_se 0
verify
```

#### 10.2 Debug 流程

1. 查看记录以寻找线索
2. 使用调试工具和命令
3. 识别并解决问题区域
4. 再次尝试验证
5. 寻求帮助


![debug_flow](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/debug_flow.png)

#### 10.3 Debug 步骤

1. 检查日志输出（Warning、Error）

    - 检查模拟和综合不匹配的错误
    - 检查 RTL 解释编译过程信息
    - full_case 和 parallel_cases 的指令是否被解释编译？
    - 检查黑盒警告信息

2.  检查 SVF guidance 处理是否存在失败的指令。

3. 检查 unmatched 的比较点

    - 不匹配的比较点是否仅在 implementation 设计中存在？
    - 是否找到 clock-gating latches？

4. 是否存在设置问题？您是否禁用了扫描链？

5. 尝试使用自动设置模式

    - set synopsys_auto_setup true

#### 10.4 Debug 工具：analyze_points

命令 analyze_points 为验证失败或超时的比较点提供 debug 指导

- 验证失败的 option：-failing、-all
- 验证超时的 option：-aborted、-unverified、-no_operator_svp、-all

对于验证超时的命令，analyze_points 命令会查看与逻辑锥相关的 datapath 特定 SVF 操作。

生成 Design Compiler Tcl 脚本命令：set_verification_priority
- 针对特定块、实例或算术运算符
- 关闭特定优化
- 提高验证成功率
- 最大限度地减少 QoR 影响

**验证失败 debug**

![debug_failed](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/debug_failed.png)

**验证超时 debug**

![debug_aborted](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/debug_aborted.png)

**GUI debug 操作**

![debug_gui1](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/debug_gui1.png)

![debug_gui2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/debug_gui2.png)

#### 10.5 Debug 工具：查看 Pattern

Formality 自动创建向量集（反例）来说明比较点的失败

– 这些反例是导致验证失败的 pattern
– 失败 pattern 应用于每个逻辑锥的输入
– 以数学方式执行非等价性证明
– 对于 passed或 aborted（超时）的比较点，不存在失败 pattern

查看逻辑锥输入和失败 pattern 可以快速识别 setup 和 match 问题，对调试非常有帮助。

![pattern_view](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/pattern_view.png)

![pattern_view2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/pattern_view2.png)

对于上面的示例，可以看到当启用了扫描链的 test_se 值为1时，验证失败，尝试 set_constant $impl/test_se 0 可以成功验证。

![pattern_view3](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/pattern_view3.png)

#### 10.6 Debug 工具：查看逻辑椎

![logic_cone1](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/logic_cone1.png)

![logic_cone2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/logic_cone2.png)

![logic_cone3](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/logic_cone4.png)

![logic_cone4](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/logic_cone4.png)

![logic_cone5](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/logic_cone5.png)

#### 10.7 从电路图中查看 RTL 源码

![rtl_source](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/rtl_source.png)

### 10.8 Don't Care 

在综合中，X 状态被视为 Don't Care ，Design Compiler可以自由选择 1 或者 0。在 Formality 中，默认情况下 x 的解释和综合相同。

变量 verify_passing_mode 可以控制 X 的比较方式
- `verification_passing_mode consistency`: Default: Ref:X = Impl:1 ; Ref:X = Impl:0
- `verification_passing_mode equality`:  Ref:X fails against Impl:1 or Impl:0

- consistency 不对称，如果 RTL-to-gates 通过，gates-to-RTL 可能会失败

- 比较 RTL 到 RTL 时模式“equality”很有用

**Formality 的 Don't Care 符号**

![dont_care](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/lec/image/dont_care.png)

- 当Don't Care (图中 DC) 引脚为 1 时；输出为 X。当Don't Care(图中 DC) 为 0 时；输出为 F。
