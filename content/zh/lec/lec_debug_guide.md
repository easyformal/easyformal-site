---
weight: 2
title: "LEC Debug 指南"
description: "LEC Debug 指南"

---

### 1. LEC 执行步骤

#### 1.1 读入指导文件

指导文件可以帮助 LEC 工具理解和处理设计流程中各种工具对设计所做的更改，如果没有，可能需要手动输入相关设置，这是一项耗时且容易出错的任务。

一般的综合工具都会提供此指导文件，如 Synopsys 的 DesignCompiler 会提供 svf（加密） 和 vsdc 格式的文件（set_svf、set_vsdc 命令），Cadence 的 Genus 会提供 json 格式的文件（write_do_lec 命令）。

通常该文件会记录以下信息：

- name style 综合后网表的命名风格（DFF、array、generate 等等）
- unloaded 非驱动信号
- constant 被常量优化的寄存器等
- merge 被合并优化的寄存器等等
- phase inversion 相位反转
- multibit 多位触发器
- ungroup 模块打平
- uniquify/ununiquify 模块唯一化/模块反唯一化
- datapath 数据链路（乘法、加法等等）


#### 1.2 读入 Golden 和 Revised 设计

- Golden：参考设计。通常来说可以是综合前、PR 前、ECO 前的网表等。Golden 通常意味着 RTL 和门级更改被冻结，不允许进行任何更改。  
- Revised：实现设计。通常来说是综合后、PR 后、ECO 后的网表等。

#### 1.3 Setup

前面所提的指导文件信息将在此阶段设置，除此之外，有关黑盒、scan 连接、UPF 相关约束等信息都在此阶段提供。

#### 1.4 匹配比较点

比较点（compare point）指的是进行验证时用作组合逻辑端点的设计对象。比较点包括顶层模块的输出端口、锁存器、寄存器或者黑盒输入引脚等。在验证之前，LEC 工具会将 Golden 和 Revised 的比较点进行匹配。

#### 1.5 验证

每个比较点验证后会有以下结果：Passing、Failing（Non-equivalence）、Aborted、Unverified、Not Verified。

### 2. LEC 常见问题和 Debug 技巧

#### 2.1 读取设计失败

检查设计是否缺少相关宏，elaborate 是否需要传入参数，检查 filelist 文件先后顺序（宏定义在前面）、综合库是否正确等等。  

#### 2.2 比较点匹配失败

如果匹配失败的比较点较多，优先检查指导文件（或者相关的手动设置）是否正确 。

比较点匹配失败的常见原因：

- name style 如果 Golden 和 Revised 两边命名风格的变化可能会导致比较点匹配失败  
- constant 寄存器因被常量驱动而被优化，如果两边优化不一致，会导致一边缺失，匹配失败  
- merge 寄存器被合并，可能会导致匹配失败  
- duplicate 寄存器被复制，可能会导致匹配失败  
- clock gating 综合或 PR 工具会自动添加 ICG（Integrated Clock Gating，集成时钟门控），导致一边多出一些 latch。  
- multibit reg 如果使用了 multibit reg，相应的寄存器的名称和数量会发生变化导致匹配失败
- 未约束 test/scan 信号，在比较 PR 前后的网表时，需要将 test/scan 信号设为 0 禁用扫描链。

#### 2.3 验证超时

验证超时，比较点验证 Aborted，通常是由于比较点的逻辑锥过大导致验证求解器超时，常见于包含 Datapath、乘法等的设计。如果设计包含 Datapath、乘法等内容，应按照 LEC 工具对其的验证流程处理。  

#### 2.4 比较点验证不等价

可以先使用 LEC 工具的分析诊断功能分析一下，看看有没有帮助。如果没有，接下来先分析一下逻辑锥的锥底输入是否匹配。逻辑锥的锥底输入不匹配并不意味着就是导致不等价的原因，因为设计里可能有的冗余逻辑也会导致此类情况。最后打开逻辑锥的电路图进行对比，先使用 Diagnosis 功能得到 Error Candidate（可能导致不等价的点），然后对比两边的设计逻辑进行分析。



