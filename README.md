# DREAM

## Disclaimer

This code is not supported by [Code Intelligence](https://www.code-intelligence.com). However, many of the techniques are now part of [CI Fuzz](https://www.code-intelligence.com/product-tour) to support our structure-aware fuzzing, grammar fuzzing, and structure detection.

The results have been published at [NDSS 2015](https://net.cs.uni-bonn.de/fileadmin/ag/martini/Staff/yakdan/dream_ndss2015.pdf).

## Introduction

The current implementation of DREAM is divided into two components:

1. **Part 1** is a C++ IDA plugin and performs the following analysis:

   - _IR Lifter_ lifts x86 code into DREAM IR.
   - _SSA Transformer_ transforms the Static Single Assignment (SSA) form.
   - _Data Flow Analysis_: this includes
     - Condition code translation: Transforming the flags used in conditional jump instructions into corresponding high-level conditions
     - Expression propagation: propagates definitions to their using instructions. Here, a few heuristics are used to
       avoid producing overly complex expressions
     - Dead code elimination: It removes dead code.
   - _Type Analysis_ recovers elementary types of recovered variables in the function. The implementation is based on
     concepts presented in the TIE paper.
   - _SSA back translation_ transforms the code out of SSA form. This includes removing the phi functions by representing
     their semantics using normal IR code.

   The analysis results of the first part can be exported into a JSON file (check the description of the format of the JSON file).

2. **Part 2** is python program that parses the exported JSON file and then perform the following analysis:
   - _Control-Flow Structuring_ to recover the control structure of the function by analyzing the control flow graph
     in order to represent the control flow using high-level control constructs, e.g., _if-then_ and _while_ statements.
   - _Readability improvements_ include several optimizations to improve the readability of the decompiled code.

## Part 1

This gives an overview about the first part of the decompiler.

### Installation Requirements

The code is provided as Visual Studio 2010 Solution and has the following requirements:

- IDA 6.4 SDK.
- The Boost Graph Library (version 1.55.0) is used for graph algorithms.
- Windows SDK

The configurations of the solution are taken from [this tutorial](http://www.openrce.org/reference_library/files/ida/idapw.pdf).
The project is configured so that the resulted binary is stored in IDA's plugins folder.
You might need to adjust the project configurations so that the paths points to where the dependencies are installed
on your systems. Currently, the plugin is used in a Windows XP virtual machine.

### Usage

To run the plugin use the key combination `Ctrl + D`. Then a dialog box with several options will pop up.
There, you can choose to export (as a JSON file) a single function or all the functions in the binary.
In both cases you need to specify the folder where the exported function(s) will be stored.
For each function, the corresponding JSON file is named `<function name>.json`.

###JSON Format
The result of the first analysis is exported in a JSON file, which represents a binary function.

```javascript
{
    "function_name": // function name
    "arguments": // a list of all expressions representing the function arguments
    "cfg": // an object representing the cotrol flow graph of the function
}
```

#### Control Flow Graph

This represents the control flow graph of a function and has the following format:

```javascript
{
    "nodes": // the list of the CFG's nodes
    "conditions_map": // a map from edge labeles to the corresponding condition expressions
}
```

#### Node

A node represents a basic block and has the following format:

```javascript
{
    "id": // a unique number to identify the node
    "type": // the type of the node and can be either "Conditional" and "Code" (see the NDSS'15 paper)
    "successors": // a list of edges to successor nodes
    "instructions": // a list of instructions contained in the node. Clearly, this field is only available in code nodes
}
```

#### Successor Edge

An Edge represents a possible transition of control between two nodes and has the following format:

```javascript
{
    "id": // the identifier of the successor node. Note the source node is implicitly defined as the Node object containing the endge
    "tag": // the label associated of edge. It represent the condition based on which this edge is executed after the source node.
}
```

#### Instruction

An instruction entry represents a statement in DREAM IR and has the following format:

```javascript
{
    "instruction_type": // The type of statement
    "...": // remaining fields depends on the statement type (check the json parser).
}
```

#### Expression

An expression entry represents a expression in DREAM IR and has the following format:

```javascript
{
    "expression_type": // The type of expression
    "...": // remaining fields depends on the expression type (check the json parser).
}
```

## Part 2

This gives an overview about the second part of the decompiler.

### Installation Requirements

- Some of the dependencies are pip-installable

  ```bash
  pip install -r requirements.txt
  ```

- install z3 with Python bindings. Several installations options are possible and explained
  ```bash
  git clone https://github.com/Z3Prover/z3.git
  cd z3
  python scripts/mk_make.py --python
  cd build
  make
  sudo make install
  ```
- Install [SWI-Prolog](http://www.swi-prolog.org) and
  the python library [pyswip](https://github.com/yuce/pyswip) (version 0.2.3).

      Installing SWI-Prolog is available as a package for most major Linux distributions.
      Installation steps are explained [here](http://www.swi-prolog.org/build/LinuxDistro.txt).

      The pip-installable version of pyswip is 0.2.2. For this reason, it was excluded from the requirements.txt file.
      To install pyswip ```python setup.py install```

- Install the graph_tool library. Installation steps are explained [here](https://graph-tool.skewed.de/download)

### Usage

To run the decompiler, you can use the following command:

```bash
python dream.py (--decompile|--compile-transformation-rules) -i <input file> -o <output file/directory> [--json] [--split-returns]
```

There are two modes available

1.  **_decompile_**: in this mode a function is chosen to be decompiled. Available options for this mode are:

    - `-i <input file>` specifies the input file that contains the IR of the function to be decompiled.
    - `-o <output file>` specifies the output files where the decompiled code is stored.
    - `--json` specifies that the input file is in JSON format (as exported by the corresponding IDA plugin)
    - `--split-returns` this option causes return nodes (only containing return statements)
      with three or more incoming edges to be splitted into several nodes with with a single incoming edge.
      In some cases, this leads to a more readable code.

2.  **_compile-transformation-rules_**: in this mode, transformation rules are compiled into prolog rules, which DREAM
    uses to match for the defined patters and replace those patterns as defined by the corresponding transformation rule.
    Available options for this mode are:
    _ `-i <input file>` specifies the input file that contains the source code of the transformation rules.
    _ `-o <output directory>` specifies the directory where the compiled rules are stored.
    In this directory, two files are created by the compiler:
    _ `rules.pl` contains Prolog inference rules
    _ `queries` contains the corresponding queries that will be performed by the transformer (`dream/CTransformer.py`)

        The main configurations of DREAM are stored in ``dream/config.py``. Current configurations use the rules contained
         in ``dream/prolog``.
