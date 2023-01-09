* Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

# Ocaml code extraction and test for these matrix models.

## 1. Test method

* Test content

  * Correct of matrix multiplication
  * Efficient of this operation
  * cont.

* Test steps

  * random generate data of "float list list"
  * call "l2m" to convert the data to inner matrix model
  * call "mmul" in corresponded model to perform matrix multiplication
  * call "m2l" to convert the matrix model to "float list list"
  * print to screen

* The usage of the test program

  ```
  $ ./matrix --help
  Usage: ./test [option] where options are:
    -mm Set matrix model (DL/DP/DR/NF/FF)
    -size Set matrix dimension
    -print Show matrix content
    -benchmark Benchmark mode, automatic test
    -help  Display this list of options
    --help  Display this list of options
  ```
  
  We provided several optional parameters
  
  * mm          specify the matrix model, which could be one value from {DL,DP,DR,NF,FF}
  * size        specify the matrix dimension. For simplicity, three dimensions of two matrices have same value.
	That means: $A(r\times c) \times B(c\times s) = C (r\times s)$，r = c = s = size。
  * print       is print the matrix? Note that, we only print head informations, not all of them
  * benchmark   is perform the test benchmark? If true, the program will automatic choose the model, and auto increase the matrix size, to do a infinite test.


## 2. Test result

* Version ( Nov 04, 2022)

  * Conclusion：All matrix models could be extracted ocaml code, but the efficient have big difference.

  * Correctness：NF model is wrong (not implemented yet), other four models are correct.

    * We use same input (same data of the input matrix), we get the correct result for multiplication operation of top four models.
    * But the NF model have no result. Because the "choiceType" has a dummy implementation (I havn't understand the Mathmatical-Component project yet)

  * Efficient differences:

    We get the running time (unit: second) of matrix multiplication operation with different matrix dimension.

    The result of FF model is wrong, and very slow too. So we dont' use it now.
	Some result of FF model is (with the dummy result)

    size=10, 0.14s
    size=20, 3.50s
    size =25, 12s
    size=30, 40s

    Comparison of other models

    | size\model | DL    | DP   | DR   | NF     | FF   |
    | ---------- | ----- | ---- | ---- | ------ | ---- |
    | 20         | 0.00  | 0.00 | 0.00 | 0.00   | 3.50 |
    | 50         | 0.26  | 0.02 | 0.01 | 0.37   |      |
    | 60         | 0.52  | 0.04 | 0.02 | 0.76   |      |
    | 72         | 1.04  | 0.06 | 0.02 | 1.58   |      |
    | 86         | 2.06  | 0.10 | 0.04 | 3.22   |      |
    | 103        | 4.18  | 0.18 | 0.07 | 6.52   |      |
    | 123        | 8.42  | 0.30 | 0.12 | 13.11  |      |
    | 147        | 17.26 | 0.51 | 0.19 | 26.63  |      |
    | 176        | 34.46 | 0.86 | 0.33 | 54.43  |      |
    | 211        | 72.90 | 1.48 | 0.55 | 111.90 |      |
    | 253        |       |      |      |        |      |

    Analysis of the result:

    * Because this test method use list type as the immediate result, and depends on lots of auxiliary functions. So the result has a lot of room for improvement.
    * All the functions havn't optimized yet. For example, we havn't carefully design tail-recursion yet.
