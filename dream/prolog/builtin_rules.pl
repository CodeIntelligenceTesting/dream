/*
* Copyright (C) 2011-2017 Khaled Yakdan.
* All rights reserved.
*/

directly_after(S1, S2, Stmts):-
	nth0(Idx1, Stmts, S1),
	nth0(Idx2, Stmts, S2),
	Idx1 =:= Idx2 + 1.

after(S1, S2, Stmts):-
	nth0(Idx1, Stmts, S1),
	nth0(Idx2, Stmts, S2),
	Idx1 > Idx2.

ancestor_node(Node, Ancestor) :-
	parent_node(Node, Ancestor).

ancestor_node(Node, Ancestor) :-
	parent_node(Node, Parent),
	ancestor_node(Parent, Ancestor).

get_all_children(Node, Children) :-
	findall(Child, ancestor_node(Child, Node), Children).

common_ancestor(Node1, Node2, Ancestor) :-
	(ancestor_node(Node1, Node2), Ancestor = Node2);
	(ancestor_node(Node2, Node1), Ancestor = Node1);
	(ancestor_node(Node1, Ancestor), ancestor_node(Node2, Ancestor)).

common_ancestor_list([H|[]], H).

common_ancestor_list([H1|[H2|T]], Ancestor) :-
	common_ancestor(H1, H2, PartialAncestor),
	common_ancestor_list([PartialAncestor|T], Ancestor).

is_last_child(Node, ParentSet) :-
	member(Node, ParentSet),
	select(Node, ParentSet, Tail),
	forall(member(Parent, Tail), ancestor_node(Node, Parent)).

%nearest_common_ancestor(Nodes, CommonAncestor) :-
%	findall(Ancestor, common_ancestor_list(Nodes, Ancestor), AncestorList),
%	list_to_set(AncestorList, AncestorSet),
%	is_last_child(CommonAncestor, AncestorSet).
%------------------------------------------------------

all_ancestors(Node, Ancestors) :-
	findall(Ancestor, ancestor_node(Node, Ancestor), Ancestors).

intersect([Set|[]], Set).

intersect([Set1|[Set2|Rest]], Intersection) :-
	intersection(Set1, Set2, Set3),
	intersect([Set3|Rest], Intersection).

nearest_common_ancestor(Nodes, CommonAncestor) :-
	findall(Ancestors, (member(Node, Nodes), all_ancestors(Node, Ancestors)), AncestorsSet),
	intersect(AncestorsSet, CommonAncestors),
	max_list(CommonAncestors, CommonAncestor).

%------------------------------------------------------

symbol_uses(Symbol, Uses):-
	findall(Use, (logicIdentT(_, Use, Symbol), logicExpressionT(Use, _, _)), Uses).

multiple_symbol_uses(Symbol, Uses) :-
	logicSymbolT(SymbolId, _, Symbol),
	symbol_uses(SymbolId, Uses),
	length(Uses, UsesNum),
	UsesNum > 1.

in_sequence_ancestor(Sequence, Node, Ancestor) :-
	sequenceT(Sequence, _, Children),
	member(Ancestor, Children),
	(ancestor_node(Node, Ancestor) ; Ancestor =:= Node).

in_sequence_ancestor_set(Sequence, NodeList, AncestorSet) :-
	findall(Ancestor, (member(Node, NodeList), in_sequence_ancestor(Sequence, Node, Ancestor)), AncestorList),
	list_to_set(AncestorList, AncestorSet).


definitions(Variable, Defs) :-
	findall(Def, (assignT(Def, _, LIdent, _), identT(LIdent, Def, Variable)), Defs).

uses(Variable, Uses) :-
	definitions(Variable, Defs),
	findall(Use, (identT(_, Use, Variable), not(member(Use, Defs))), Uses).

non_preserving_use(Variable, NonPreservingUse) :-
	(assignT(NonPreservingUse, _, Lhs, _), identT(Lhs, NonPreservingUse, Variable));
	(callT(NonPreservingUse, _, _, Parameters), identT(Param, NonPreservingUse, Variable), member(Param, Parameters));
	(operationT(NonPreservingUse, _, [Ident], '&'), identT(Ident, NonPreservingUse, Variable)).


pre_order_after(AstNode1, AstNode2) :-
	pre_order_next(AstNode1, AstNode2).

pre_order_after(AstNode1, AstNode2) :-
	pre_order_next(AstNode1, AstNode1Next),
	pre_order_after(AstNode1Next, AstNode2).

pre_order_before(AstNode1, AstNode2) :-
	not(pre_order_after(AstNode1, AstNode2)),
	AstNode1 =\= AstNode2.


in_neighbours(Node, InNeighbours) :-
	findall(Pred, cfg_edge(Pred, Node), InNeighbours).

path(Source, Target, Path) :-
	travel(Source, Target, [Source], ReversedPath),
	reverse(ReversedPath, Path).

path_not_passing_by(Source, Target, NotPassingByNode, Path) :-
	travel(Source, Target, [Source], Path),
	not(member(NotPassingByNode, Path)).

travel(Source, Target, Path, [Target|Path]) :-
	cfg_edge(Source, Target).

travel(Source, Target, Visited, Path) :-
	cfg_edge(Source, Node),
	Node \== Target,
	\+member(Node, Visited),
	travel(Node, Target, [Node|Visited], Path).

exists_on_path(Node, Source, Target) :-
	path_not_passing_by(Source, Node, Target, _),
	path_not_passing_by(Node, Target, Source, _),
	!.

middle_nodes(Source, Target, NodeSet) :-
	findall(Node, (path_not_passing_by(Source, Node, Target, _), path_not_passing_by(Node, Target, Source, _)), NodeList),
	list_to_set(NodeList, NodeSet).

middle_nodes_not_passing_by(Source, Target, NotPassingByNode, NodeSet) :-
	findall(
		Node,
		(
			path_not_passing_by(Source, Node, Target, Path1),
			not(member(NotPassingByNode, Path1)),
			path_not_passing_by(Node, Target, Source, Path2),
			not(member(NotPassingByNode, Path2))),
		NodeList),
	list_to_set(NodeList, NodeSet).

single_def_single_use(Variable, Def, Use) :-
	localT(Variable, _, _),
	definitions(Variable, Defs),
	Defs = [Def|[]],
	uses(Variable, Uses),
	Uses = [Use|[]],
	not(operationT(Use, _, _, '&')),
	sequenceT(Sequence, _, Children),
	assignT(Def, Sequence, _, _),
	in_sequence_ancestor(Sequence, Use, UseAncestor),
	after(UseAncestor, Def, Children).

	%nearest_common_ancestor([Def, Use], CommonAncestor),
	%sequenceT(CommonAncestor,_, _),
	%in_sequence_ancestor(CommonAncestor, Def, InSeqStart),
	%in_sequence_ancestor(CommonAncestor, Use, InSeqEnd).

condition_with_ternary_operation(Condition, Parent) :-
	operationT(Condition, Parent, [Lhs, Rhs], OpString),
	(OpString = '==' ; OpString = '!='),
	(ternaryOperatorT(Lhs, Condition, _, _, _); ternaryOperatorT(Rhs, Condition, _, _, _)).

endless_to_while(Loop, NegatedCondition) :-
	loopT(Loop, _, 'endless', _, Body),
	sequenceT(Body, Loop, [ConditionalBreak|_]),
	ifT(ConditionalBreak, Body, NegatedCondition, Break, 'null'),
	breakT(Break, ConditionalBreak).

is_assignment_to_variable(Assignment, Variable) :-
	assignT(Assignment, _, Lhs, _),
	identT(Lhs, Assignment, Variable).

is_call_using_variable(Call, Variable) :-
	callT(Call, _, _, Parameters),
	identT(Ident, Call, Variable),
	member(Ident, Parameters).

preserved_variable(Variable, StatementList) :-
	forall(member(Statement, StatementList),
			not(is_assignment_to_variable(Statement, Variable);is_call_using_variable(Statement, Variable))
	).

preserved_variable_list(VariableList, StatementList) :-
	forall(member(Variable, VariableList), preserved_variable(Variable, StatementList)).


%only for renaming loop variables
counting_loop(Loop, CountingVariableSet) :-
	((
		forT(Loop, _, InitStatements, _, _, _),
		findall(
			Variable,
			(
				assignT(InitStmt, Loop, Lhs, _),
				member(InitStmt, InitStatements),
				identT(Lhs, InitStmt, Variable)
			),
			CountingVariableList
		)
	);
	(
		loopT(Loop, _, _, LoopCondition, LoopBody),
		sequenceT(LoopBody, Loop, BodyChildren),
		findall(
			Variable,
			(
				localT(Variable, _, _),
				identT(IdentCond, _, Variable),
				identT(IdentBody, _, Variable),
				assignT(UpdateStmt, LoopBody, IdentBody, _),
				member(UpdateStmt, BodyChildren),
				ancestor_node(IdentCond, LoopCondition)
			),
			CountingVariableList
		)
	)),
	list_to_set(CountingVariableList, CountingVariableSet),
	length(CountingVariableSet, Size),
	Size > 0.

counting_loops(LoopList) :-
	findall([Loop, VariableList], counting_loop(Loop, VariableList), LoopList).

array_index(Index) :-
	arrayIndexingT(_, _, _, Ident),
	identT(Ident, _, Index).

is_last_in_pre_order(Node, NodeSet) :-
	member(Node, NodeSet),
	select(Node, NodeSet, Tail),
	forall(member(PreNode, Tail), pre_order_before(Node, PreNode)),!.

dead_in_statement(Variable, Statement) :-
	get_all_children(Statement, Children),
	forall(member(Child, Children), Child \= identT(_, _, Variable)).

dead_in_statements(Variable, StatementList) :-
	forall(member(Statement, StatementList), dead_in_statement(Variable, Statement)).

variables_dead_in_statements(VariableList, StatementList) :-
	forall(member(Variable, VariableList), dead_in_statements(Variable, StatementList)).

for_init_statement(Variable, ForLoop, InitStatement, IntermediateStatements):-
	findall(
		InitStatement,
		(
			sequenceT(Sequence, _, Children),
			assignT(InitStatement, Sequence, InitLhs, _),
			identT(InitLhs, InitStatement, Variable),
			member(InitStatement, Children),
			in_sequence_ancestor(Sequence, ForLoop, ForLoopAncestor),
			after(ForLoopAncestor, InitStatement, Children)
		),
		InitStatementCandidates
	),
	is_last_in_pre_order(InitStatement, InitStatementCandidates),
	middle_nodes(InitStatement, ForLoop, IntermediateStatements),
	dead_in_statements(Variable, IntermediateStatements).

for_loop(ForLoop, ForVariableList) :-
	loopT(ForLoop, _, 'while', LoopCondition, LoopBody),
	sequenceT(LoopBody, ForLoop, BodyChildren),
	findall(
		[Variable, InitStatement, AfterInitStatements, UpdateStatement, AfterUpdateStatementList],
		(
			localT(Variable, _, _),
			identT(IdentCond, _, Variable),
			ancestor_node(IdentCond, LoopCondition),
			identT(IdentBody, _, Variable),
			assignT(UpdateStatement, LoopBody, IdentBody, _),
			nth0(StartIdx, BodyChildren, UpdateStatement),
			findall(NextStatement, (nth0(Idx, BodyChildren, NextStatement), Idx > StartIdx), AfterUpdateStatementList),
			dead_in_statements(Variable, AfterUpdateStatementList),
			for_init_statement(Variable, ForLoop, InitStatement, AfterInitStatements)
		),
		ForVariableListDuplicates
	),
	sort(ForVariableListDuplicates, ForVariableList),
	length(ForVariableList, Size),
	Size > 0.

break_to_return(Break, BreakParent, Return) :-
	breakT(Break, BreakParent),
	cfg_edge(Break, Return),
	returnT(Return, _, _).

%return_result(Variable) :-
%	findall(Ret, returnT(Ret, _, _), ReturnStmts),
%	list_to_set(ReturnStmts, ReturnStmtsSet),
%	ReturnStmtsSet = [Return|[]],
%	returnT(Return, _, Ident),
%	identT(Ident, Return, Variable),
%	localT(Variable, _, _).

return_result(Variable) :-
	findall(Var, returned_variable(Var), ReturnedVars),
	list_to_set(ReturnedVars, ReturnedVarsSet),
	ReturnedVarsSet = [Variable|[]].

returned_variable(Variable) :-
	returnT(Return, _, Ident),
	identT(Ident, Return, Variable),
	localT(Variable, _, _).

memory_variable(Pointer) :-
	memoryT(Mem, _, Address),
	(
		(
			identT(Address, Mem, Pointer),
			localT(Pointer, _, _)
		);
		(
			operationT(Address, Mem, Operands, '+'),
			length(Operands, 2),
			identT(Op1, Address, Pointer),
			localT(Pointer, _, _),
			numericLiteralT(Op2, Address, _),
			member(Op1, Operands),
			member(Op2, Operands)
		)
	).

related_integer(Pointer, RelatedInteger) :-
	operationT(Add, _, Operands, '+'),
	length(Operands, 2),
	identT(IdentPtr, Add, Pointer),
	member(IdentPtr, Operands),
	identT(IdenInt, Add, RelatedInteger),
	localT(RelatedInteger, _, _),
	member(IdenInt, Operands),
	IdentPtr \= IdenInt.

related_pointer(Pointer, RelatedPointer) :-
	assignT(Assignment, _, Lhs, Rhs),
	(
		(
			identT(Lhs, Assignment, Pointer),
			identT(Rhs, Assignment, RelatedPointer),
			localT(RelatedPointer, _, _)
		)
		;(
			identT(Rhs, Assignment, Pointer),
			identT(Lhs, Assignment, RelatedPointer),
			localT(RelatedPointer, _, _)
		)
	).

find_declaration(Variable, Defs, Uses, CommonAncestor) :-
	localT(Variable, _, _),
	definitions(Variable, Defs),
	length(Defs, DefsSize),
	DefsSize >= 0,
	uses(Variable, Uses),
	append(Defs, Uses, Occurences),
	nearest_common_ancestor(Occurences, CommonAncestor).

same_expression(Exp1, Exp2) :-
	identT(Exp1, _, V),
	identT(Exp2, _, V).

same_expression(Exp1, Exp2) :-
	numericLiteralT(Exp1, _, V),
	numericLiteralT(Exp2, _, V).

same_expression(Exp1, Exp2) :-
	memoryT(Exp1, _, Addr1),
	memoryT(Exp2, _, Addr2),
	same_expression(Addr1, Addr2).


may_array_access(Pointer, Parent) :-
	memoryT(Pointer, Parent, Address),
	operationT(Address, Pointer, _, '+').

address_expression_to_pointer(Variable, Def, Uses) :-
	localT(Variable, _, _),
	definitions(Variable, Defs),
	Defs = [Def|[]],
	uses(Variable, Uses),
	forall(member(Use, Uses), operationT(Use, _, _, '&')).

% simplifying conditions
set_all_bits_expect_first_and_last(Assign, Parent, V, Exp) :-
    assignT(Assign, Parent, Lhs, Rhs),
    identT(Lhs, Assign, V),
    operationT(Rhs, Assign, Operands, '&'),
    length(Operands, 2),
   	numericLiteralT(Const, Rhs, 2147483649),
   	member(Const, Operands),
   	member(Exp, Operands),
   	Exp \= Const.

logical_and_or(Exp, Parent) :-
	operationT(Exp, Parent, _, Op),
	(Op = '||' ; Op = '&&').

condition(Cond, Parent) :-
	ifT(Parent, _, Cond, _, _).

condition(Cond, Parent) :-
	loopT(Parent, _, _, Cond, _).

condition(Cond, Parent) :-
	ternaryOperatorT(Parent, _, Cond, _, _).

condition(Cond, Parent) :-
	assignT(Parent, _, _, Cond),
	operationT(Cond, Parent, _, Op),
	(Op = '||' ; Op = '&&'; Op = '=='; Op = '!='; Op = '>='; Op = '>'; Op = '<='; Op = '<').

equality_comparison(Exp, Parent) :-
	operationT(Exp, Parent, _, Op),
	(Op = '!=' ; Op = '==').

if_do_while(ParentId, If, DoWhile) :-
    ifT(If, ParentId, _, DoWhile, 'null'),
    loopT(DoWhile, If, 'doWhile', _, _).

if_do_while_init(ParentId, If, DoWhile) :-
    ifT(If, ParentId, IfCondition, DoWhile, 'null'),
    loopT(DoWhile, If, 'doWhile', LoopCondition, _),
    operationT(LoopCondition, DoWhile, [Ident1, Ident2], '<'),
    identT(Ident1, LoopCondition, Var1),
    identT(Ident2, LoopCondition, Var2),
    operationT(IfCondition, If, [Ident3, Zero], Op),
    identT(Ident3, IfCondition, Var2),
    numericLiteralT(Zero, IfCondition, 0),
    (Op = '!=' ; Op = '>'),
    sequenceT(ParentId, _, Ops),
    findall(Def, (assignT(Def, ParentId, Lhs, _), identT(Lhs, Def, Var1), member(Def, Ops), after(If, Def, Ops)), DefsInSequence),
    DefsInSequence = [Init|[]],
    assignT(Init, ParentId, _, Zero2),
    numericLiteralT(Zero2, Init, 0).

do_while_to_while(ParentId, DoWhile, Init) :-
    loopT(DoWhile, ParentId, 'doWhile', LoopCondition, _),
    operationT(LoopCondition, DoWhile, [Ident1, Const1], _),
    identT(Ident1, LoopCondition, Var1),
    numericLiteralT(Const1, LoopCondition, _),
    sequenceT(ParentId, _, Ops),
    findall(Def, (assignT(Def, ParentId, Lhs, _), identT(Lhs, Def, Var1), member(Def, Ops), after(DoWhile, Def, Ops)), DefsInSequence),
    DefsInSequence = [Init|[]],
    assignT(Init, ParentId, _, Const2),
    numericLiteralT(Const2, Init, _).

shift_expression(Shift, ParentId) :-
	operationT(Shift, ParentId, [_, Const], Op),
	(Op = '>>' ; Op = '<<'),
	numericLiteralT(Const, Shift, _).

for_loop(ForLoop) :-
	forT(ForLoop, _, _, _, _, _).

nested_for_loops(UpperStmt, InnerForLoops) :-
	findall(ForLoop, (for_loop(ForLoop), ancestor_node(ForLoop, UpperStmt)), InnerForLoops).

only_used_in_statement(Variable, Stmt) :-
	uses(Variable, Uses),
	forall(member(Use, Uses), ancestor_node(Use, Stmt)).