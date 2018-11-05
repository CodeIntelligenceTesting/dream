/*
* Copyright (C) 2011-2017 Khaled Yakdan.
* All rights reserved.
*/

named_constant_compare(Value, Compare) :-
	operationT(Compare, _, [_, Const], Op),
	numericLiteralT(Const, Compare, Num),
	Num = Value,
	(Op = '==' ; Op = '!=').