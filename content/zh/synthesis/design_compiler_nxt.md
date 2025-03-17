---
weight: 2
title: "DC 高级综合技术"
description: "高级综合优化技术"
draft: true
---


### 0. 最佳综合结果的要求

以下内容对于综合以满足积极的时序目标和良好的布局后关联性至关重要。

- 高质量的 RTL 代码

- 完整准确的约束

- 使用所有适用的 DC NXT Ultra 优化技术进行编译

- 利用 DC NXT physical guidance 功能

为了简化综合流程，尽可能自上而下地编译大的 design（block）

- 需要更少的 block 约束文件、编译和迭代


Synthesis Optimization Overview

Auto ungrouping
Boundary optimization
Test-ready synthesis
Adaptive retiming
High effort timing
Prioritizing setup timing over DRCs
Disabling DRC fixing on clock network
User-defined path groups
TNS-driven placement
Pipeline or register retiming
Multi-core optimization
Disabling runtime intensive settings
Final area recovery


### 1. compile_ultra 默认的优化

执行三个级别的优化：

+ 架构级或高层次综合
+ 逻辑级或 GTECH 优化
+ 门级或 mapping 优化

优化重点：逻辑 DRC 和时序（最小化面积而不影响其他逻辑）

默认情况下，compile_ultra 使用 max_area 约束为零，与时序、设计规则或功率约束相比，面积约束在优化过程中始终具有最低优先级。

### 2. DesignWare 库介绍

DesignWare 是 soft IP 和Datapath 组件的集合，DesignWare 库在 compile_ultra 阶段会自动包含在`synthetic_library` 和 `link_library` 中。

DC 自动推断 RTL 代码中的运算符（+、-、*、>、=、<）并使用相应的 DesignWare  组件。

### 3. 单一算术优化

- DesignWare 库支持使用 Datapath 生成器来构建许多不同的算术运算符实现（+、-、*、>、=、<、<=、>=）
- 多种实现允许 compile_ultra 为设计中的每个单例运算符选择最佳实现（满足时序的最小实现）
- 一旦选定，每个实现都会针对目标技术库进行优化

Datapath 生成器动态地为每个算术符构建适当的实现（满足时序的最小实现），而不是从一组预先构建的“静态”架构中选择一个实现。


### 4. Datapath 优化：CSA 转换

CSA 转换产生最有效的算术电路——更小更快


### 5. 算术表达式优化

- 常量/操作数折叠

```
  A + 2*B - 2 + B -A + 7    ->    3*B + 5
```
- 公共子表达式共享
```
      Z1 = A + B + C; Z3 = C + D + B;
->  T = B + C; Z1 = A + T; Z2 = T + D;
```
- SOP -> POS 转换
```
        A * C + B*C     ->      (A+B) * C
```
- 比较器共享
```
Z1  =   A>B;    Z2 = A<B;   Z3 = A <=B;
-> 使用单个减法器，具有多个比较输出
```
- 并行常数乘法器优化

```
        Temp = In1 + In2;   Out1 = Temp * 105;  Out2 = Temp * 621
->     Out1 = (Temp << 6) + (Temp<<5) + (Temp<<3) + Temp;
->      Out2= (Out1) +(Temp<<9) + (Temp<<2)

//  105=64+32+8+1, 621=105+512+4
```

### 6. 关键路径再综合

关键路径再综合会根据需要自动调用：包含顽固、违反关键路径的映射逻辑锥被返回到逻辑级优化，然后重新映射，反复进行

### 7. 负载分配和组合逻辑复制

负载分配和逻辑复制减少了关键路径的延迟，导致更快（但更大）的电路。

组合逻辑复制总是被启用，并根据需要应用以提高时序，不能关闭。

### 8. 库分析


### 9. Auto Ungrouping

### 10. Boundary Optimization

### 11. Design Partitaioning

### 12. Scan Register

### 13. 自动识别移位寄存器

### 14. 自适应 Retiming

### 15. High-Effort Timing Optimization

### 16. Prioritizing Setup Timing over DRCs

### 17. Clock Network: Default DRC-Disabling

### 18. Disabling DRCs on Entire Clock Network

### 19. Solution: User-Defined Path Groups

### 20. Enabling Near-Critical Path Optimization

### 21. Multi-Clock Example

### 22. TNS-Driven Placement

### 23. Reducing Large Datapath Delay

### 24. Pipeline or Register Retiming

### 25. Optimization Phases of Register Retiming


### 26. Separate Pipeline Hierarchies

### 27. Threshold Optimizatic

### 28. Multi-Core Optimizatior

### 29. pisabling Runtime-intensive Settings

### 30. Subseguent Incremental Compile

