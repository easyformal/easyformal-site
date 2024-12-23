---
title: "问题：如何选择数组？"

tags: "sv"

weight: 21
---

## 固定数组/静态数组：

**1) 固定数组优于所有其他类型的数组：**

- 固定数组比所有其他类型的数组执行速度更快（即关联数组、动态数组、队列），因为它将存储在内存的未初始化数据段（bss段）中，所以执行时将消耗较少的模拟时间。堆是动态、关联和队列内存分配的段。
下图显示了内存布局。

![memory_segments](https://user-images.githubusercontent.com/110448056/188258335-c478ebd9-4785-415d-9873-cbf6269eecd4.png)

- 如果大小事先已知，那么我们可以选择固定数组而不是所有其他类型的数组。

## 动态数组：

**1) 动态数组优于固定数组：**

- 在运行时分配内存，因此内存不会被浪费，但在固定数组中，当我们不知道实际大小时，内存会被浪费。
- 我们可以使用 `new()` 方法轻松添加元素，但在固定数组中，我们不能在声明后添加元素。
- 在为其分配内存后，我们可以删除整个数组，但在固定数组中，我们不能在声明数组后删除内存。

**注意：** 在固定数组中，没有 `new()`、`delete()` 等方法。

**2) 动态数组优于关联数组：**

- 索引是连续的，但在关联数组中是不连续的。如下图所示。

![indexing](https://user-images.githubusercontent.com/110448056/188263690-151e9f91-36a8-4b2e-baf6-42505a1f7fc1.png)

- 我们可以找到索引之间的关系，因此可以轻松使用循环遍历数组，但在关联数组中需要键。

**3) 动态数组优于队列：**

- 根据内存占用量，动态数组执行速度更快，并且需要较少的模拟时间，但队列需要更长的执行时间。

![dynamic-1](https://user-images.githubusercontent.com/110448056/188267346-99ee256d-34b8-4946-92b6-4ecf42d368d4.png)

![queue-1](https://user-images.githubusercontent.com/110448056/188267352-d9bba19f-cf55-41fa-8646-2b907fabcb67.png)

- 动态数组用于使用循环跟踪数组中的每个元素，但在队列中，通过弹出和推送操作，我们无法使用 `foreach` 循环跟踪数组的所有元素。对于弹出操作，数组的大小会减少，而索引会增加；对于推送操作，数组的大小会增加，索引也会增加，导致进程被终止。
 
code:

      module dynamic;
      int dyn [];
      initial
      begin
      dyn = new[8];
      dyn = '{2,7,0,6,1,9,9,7};
      foreach(dyn[i])begin
        $display("verifying the values of each index, dyn[%0d] = %0d", i, dyn[i]);
      end
      end
      endmodule 

OUTPUT:  

     run -all
     verifying the values of each index, dyn[0] = 2  
     verifying the values of each index, dyn[1] = 7  
     verifying the values of each index, dyn[2] = 0  
     verifying the values of each index, dyn[3] = 6  
     verifying the values of each index, dyn[4] = 1  
     verifying the values of each index, dyn[5] = 9  
     verifying the values of each index, dyn[6] = 9  
     verifying the values of each index, dyn[7] = 7  
     exit  

  
code: using pop operation

     `module queue;
     int que[$];
     initial
     begin
      que = '{2,7,0,6,1,9,9,7};
      foreach(que[i])begin
      $display("verifying the values of each index, que[%0d] = %0d", i, que[i]);
      que.pop_back();
      end
      end 
   endmodule

OUTPUT:  

     run -all  
     verifying the values of each index, que[0] = 2  
     verifying the values of each index, que[1] = 7  
     verifying the values of each index, que[2] = 0  
     verifying the values of each index, que[3] = 6  
     exit  

code: using push operation in queue

     module queue;
     int que[$];
     initial
     begin
     que = '{2,7,0,6,1,9,9,7};
     foreach(que[i])begin
     $display("verifying the values of each index, que[%0d] = %0d", i, que[i]);
         que.push_back(6);
     end
     end
     endmodule 

OUTPUT:

    `run -all
     verifying the values of each index, que[0] = 2
     verifying the values of each index, que[1] = 7
     verifying the values of each index, que[2] = 0
     verifying the values of each index, que[3] = 6
     verifying the values of each index, que[4] = 1
     verifying the values of each index, que[5] = 9
     verifying the values of each index, que[6] = 9
     verifying the values of each index, que[7] = 7
     verifying the values of each index, que[8] = 6
     verifying the values of each index, que[9] = 6
     verifying the values of each index, que[10] = 6
     verifying the values of each index, que[11] = 6
     verifying the values of each index, que[12] = 6
     Result reached the maximum of 5000 lines. Killing process.
     Execution interrupted or reached maximum runtime.

---
## 关联数组：

**1) 关联数组相对于所有其他数组的优势：**

- 在关联数组中，使用 `exists(input index)` 方法来查找索引元素，而在关联和动态数组中不使用此方法。

code:  

    module associative;           
    int id[int];    
    int name[string];    
    int value[int];     
    initial    
    begin    
      id = '{4275:25, 4278:12};    
      name = '{"Dilip":12};    
      value = '{50000:25};  
      //check whether the name exist  
      name.exists("Dilip");  
      $display("the element exist= %0p", name);  
    end  
    endmodule 

OUTPUT:   
 
     run -all    
     the element exist= {"Dilip":12}   
     exit 

* 在动态数组和队列中，没有像 **function exists(input index)** 这样的方法来查找数组元素，如果我们在动态数组中使用 **function exists(input index);**，会出现以下错误：

动态数组：

code:  

      module dynamic;
      int dyn [];
      initial
       begin
      dyn = new[8];
      dyn = '{2,7,0,6,1,9,9,7};
      dyn.exists(0);
      $display("the element of the dyn=%0p", dyn);
      end
    endmodule 

OUTPUT:  

       -- Compiling module dynamic
        ** Error (suppressible): (vlog-13276) testbench.sv(7): Could not find field/method name (exists) in 'dyn' of 'dyn.exists'.  
        ** Error (suppressible): (vlog-13276) testbench.sv(7): Could not find field/method name (exists) in 'dyn' of 'dyn.exists.$0'.  
       End time: 02:35:57 on Sep 03,2022, Elapsed time: 0:00:00  
       Errors: 2, Warnings: 0  


Queue :

code:

    module queue;
     int que[$];
     initial
    begin
      que = '{2,7,0,6,1,9,9,7};
      que.exists(0);
      $display("the element of the que=%0p", que);
    end
  endmodule

OUTPUT:  

    -- Compiling module queue    
     ** Error (suppressible): (vlog-13276) testbench.sv(6): Could not find field/method name (exists) in 'que' of 'que.exists'.  
     ** Error (suppressible): (vlog-13276) testbench.sv(6): Could not find field/method name (exists) in 'que' of 'que.exists.$0'.  
     End time: 02:43:56 on Sep 03,2022, Elapsed time: 0:00:00
     Errors: 2, Warnings: 0

---

**2) 关联数组相对于动态数组和队列的优势：**

- 在关联数组中，索引类型可以是任何数据类型，但在动态数组和队列中，我们不能使用不同的数据类型作为索引。

code:

    module associative;
    int id[int];
    int name[string];
    int value[int];
    initial
     begin
      id = '{4275:25, 4278:12};
      name = '{"Dilip":12};
      value = '{50000:25};
      $display("The id is =  {%0p}", id);
      $display("The name is =  %0p", name);
      $display("The value is =  %0p", value);
    end 
   endmodule

OUTPUT:  

     run -all  
     The id is =  {{4275:25} {4278:12} }  
     The name is =  {"Dilip":12}   
     The value is =  {50000:25}   
     exit  

---
**3) 关联数组相对于动态数组和固定数组的优势：**

- 我们可以使用 **function void delete(input index);** 在关联数组中删除特定索引元素，但在动态数组和固定数组中，我们不能使用 **function void delete(input index);** 来删除特定索引。

code:

    module associative;
    int id[int];
    int name[string];
    int value[int];
    initial
    begin
      
      id = '{4275:25, 4278:12};
      name = '{"Dilip":12};
      value = '{50000:25};
      $display("The id is =  {%0p}", id);
      $display("The name is =  %0p", name);
      $display("The value is =  %0p", value);
      $display("The size of the id is=%0d", id.size());
      id.delete(4278);
      $display("The size of 'id' after deleting = %0d", id.size());
      $display("The id is = {%0p}", id);
     end
    endmodule 

OUTPUT:   

     run -all  
     The id is =  {{4275:25} {4278:12} }  
     The name is =  {"Dilip":12}   
     The value is =  {50000:25}   
     The size of the id is=2  
     The size of 'id' after deleting = 1  
     The id is = {{4275:25} }  
     exit  

* The Associative array is memory friendly we can store the value of the array in any memory location.

---
## 队列：

**1) 队列相对于所有数组的优势：**

- 在队列中，主要优势是推送和弹出操作。
- 推送用于将元素插入队列。
- 推送有两种方法：**function push_back(input element_t);** 和 **function push_front(input element_t);**
- 弹出有两种方法：**function pop_front();** 和 **function pop_back();**

code:   

    `module queue_data_type;
     string queue1[$];
    initial 
     begin
     queue1 = {"manipal", "banglaore", "udupi"};
      $display("\nRemove the array element at first index position of queue1:%p",queue1.pop_front());
      $display("\n After removing the 'manipal' from queue1 is :%p", queue1);
      $display("\nRemove the array element at last index position of queue1: %p", queue1.pop_back());
      $display("\n After removing the 'udupi' from queue1 is :%p", queue1);
      queue1.push_front("Yelahanka");
      $display("\ninsert the array element at first index position of queue1:output");
      $display("\n queue1: %p", queue1);
      queue1.push_back("udupi");
       $display("\ninsert the array element at last index position of queue1: ouptut");
       $display("\n queue1 : %p", queue1);
    end 
  endmodule
  

OUTPUT:

    `run -all  
     // Remove the array element at first index position of queue1:"manipal"  

     // After removing the 'manipal' from queue1 is :'{"banglaore", "udupi"}  
 
     // Remove the array element at last index position of queue1: "udupi"  
  
    // After removing the 'udupi' from queue1 is :'{"banglaore"}  
 
    // insert the array element at first index position of queue1:output  
 
    // queue1: '{"Yelahanka", "banglaore"}  
 
    // insert the array element at last index position of queue1: ouptut  

    // queue1 : '{"Yelahanka", "banglaore", "udupi"}  
    exit

------
  
**2) 队列相对于动态数组和关联数组的优势：**

- 在队列中，我们可以使用方法 **function insert(index, queue_element);** 在任意索引位置插入元素。因此，我们可以说插入操作很容易。因此，即使我们从中间移除或添加元素，队列的长度也会增加和缩减，但在动态数组和关联数组中，我们无法在数组中插入元素。

code:

     `module queue_data_type;
      string queue1[$];
      int queue2[$];
     initial 
     begin
     queue1 = {"banglaore", "udupi"};
       queue1.insert(0, "manipal");
      $display("Insert the array element at 0 index position of queue1: {%0p}", queue1);
     end 
    endmodule

OUTPUT:

      `run -all      
      // Insert the array element at 0 index position of queue1: {{manipal} {banglaore} {udupi}}  
      exit  
---
