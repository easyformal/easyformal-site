---
weight: 4
title: "Safety Properties and Liveness Properties"
description: "Safety Properties and Liveness Properties；Safety 属性和 Liveness 属性；"
---

### Safety Properties

**Safety**: Ensures that bad things never happen. Examples include:
- FIFO does not overflow.
- The system does not allow multiple processes to modify shared memory simultaneously.
- A request receives a response within 5 clock cycles.

Formally, a safety property ensures that any violation has a finite prefix such that every extension of this prefix also violates the property. Safety properties can be falsified using finite simulation runs.

### Liveness Properties

**Liveness**: Guarantees that good things eventually happen. Examples include:
- A decoding algorithm eventually terminates.
- Every request eventually receives an acknowledgment.

Formally, a liveness property ensures that any finite path can be extended to satisfy the property. 

![liveness](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/liveness.png)

**Assertion:** Property P must eventually hold true after a triggering event occurs.

![liveness2](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/liveness2.png)

Theoretically, liveness properties can only be falsified using infinite simulation runs. In practice, we often assume "graceful test termination" to represent infinite time.

- If the good event does not occur within the test duration, we assume it will never occur, and the property is considered falsified.

#### Bounded Liveness

![bounded_liveness](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/bounded_liveness.png)

**Assertion:** Property P must hold true after the start trigger event and before the end trigger event.

#### Invariants

![invariant](https://cdn.jsdelivr.net/gh/easyformal/easyformal-site@master/content/zh/sva/image/4/invariant.png)

**Invariant Assertion Window:** Property P is checked and expected to hold after the start event occurs, and continues to be checked until the end event occurs.

