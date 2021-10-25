# fc

Class.hs  
提供了对解析子的通用性质，用类来描述

Combinators.hs 
提供了大部分实用的通用解析子，完成普通任务只需要其中部分解析子，完成特定的任务需要单独实现特定的解析子。

Components.hs  
在本次实验中，使用的特定的解析子，用来识别字符串

TypeLogic.hs 
用于提供类型逻辑计算的功能，通用部分，不需要改动。

Example1.hs  
算术运算表达式（PEG）示例

\color{blue}{Example2.hs} 
内存模型示例，含有一个完整的构建模型示例
