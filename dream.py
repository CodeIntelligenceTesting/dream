# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

import sys
import getopt
from dream.CTransformer import CTransformer
from dream.ControlFlowTree import ControlFlowTree, SequenceNode
from dream.RuleCompiler import RuleCompiler
from dream.ir.ast import AST
from dream.json_parser import JsonGraphParser


def decompile_json(in_file, out_file, split_returns=True):
    j_parser = JsonGraphParser()
    j_parser.graph_from_json(in_file)

    cfg = j_parser.cfg
    cfg.remove_empty_code_nodes()

    # print "structuring"
    cfg.function_signature = j_parser.get_function_signature()
    if cfg.num_vertices() == 0:
        ast = AST(SequenceNode(True, []), cfg.function_signature)
        ast.write(out_file)
        return

    cfg.merge_congruent_variables()
    cfg.structure(split_returns)

    # print "side effects"
    cft = ControlFlowTree(None)
    ast_root = cfg.vertex_properties['ast'][cfg.vertex(0)]
    cft.root = ast_root
    cft.conditions_map = cfg.conditions_map
    cft.replace_basic_blocks_by_sequence(ast_root)
    cft.combine_sequence_nodes_with_sequence_children(ast_root)
    ast = AST(ast_root, cfg.function_signature)

    c_transformer = CTransformer()
    c_transformer.set_ast(ast)
    c_transformer.remove_side_effects(cft.conditions_map)
    cft.replace_logic_symbols_by_conditions(ast_root)
    c_transformer.apply_transformations()
    ast.write(out_file)


def compile_transformation_rules(in_file, out_dir):
    r_compiler = RuleCompiler(in_file, out_dir)
    r_compiler.compile()


def print_help_message():
    print 'dream.py (--decompile|--compile-transformation-rules) ' \
          '-i <input file> -o <output file/directory> [--json] [--split-returns]'


def main():
    try:
        opts, args = getopt.getopt(sys.argv[1:], 'i:o:h',
                                   ['json', 'split-returns', 'decompile', 'compile-transformation-rules', 'help'])
    except getopt.GetoptError:
        print_help_message()
        sys.exit(2)

    opts = dict(opts)

    if '-h' in opts or '--help' in opts:
        print_help_message()
        exit(0)

    assert '-i' in opts and '-o' in opts
    in_file, out_path = opts['-i'], opts['-o']
    if '--decompile' in opts:
        split_returns = '--split-returns' in opts
        if '--json' in opts:
            decompile_json(in_file, out_path, split_returns)
    elif '--compile-transformation-rules' in opts:
        compile_transformation_rules(in_file, out_path)


if __name__ == '__main__':
    main()
