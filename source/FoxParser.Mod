MODULE FoxParser;   (**  AUTHOR "fof & fn"; PURPOSE "Oberon Compiler: Parser";  **)
(* (c) fof ETH Zurich, 2009 *)

IMPORT Basic := FoxBasic, Scanner := FoxScanner, D := Debugging, SyntaxTree := FoxSyntaxTree, Global := FoxGlobal,  Diagnostics;

CONST
	Trace = FALSE;
	CascadedWithSupport = FALSE;
	Lax=FALSE;

	(** the parser reflects the following EBNF:

		Module               = 'module' Identifier ['in' Identifier]';' [ImportList] DeclarationSequence [Body]
		                       'end' Identifier '.'.

		ImportList           = 'import' Import { ',' Import } ';'.

		Import               = Identifier [':=' Identifier] ['in' Identifier].

		DeclarationSequence  =
		                        { 'const' [ConstDeclaration] {';' [ConstDeclaration]}
		                         |'type'  [TypeDeclaration] {';' [TypeDeclaration]}
		                         |'var'   [VariableDeclaration] {';' [VariableDeclaration]}
		                        }
		                        [ProcedureDeclaration | OperatorDeclaration]
		                        {';' [ProcedureDeclaration | OperatorDeclaration] }.

		ConstDeclaration     = IdentifierDefinition '=' Expression.

		TypeDeclaration      = IdentifierDefinition '=' Type.

		VariableDeclaration  = VariableNameList ':' Type.

		ProcedureDeclaration = 'procedure' ['&'|'-'|Flags ['-']] IdentifierDefinition [FormalParameters]';'
		                       DeclarationSequence  [Body] 'end' Identifier.

		OperatorDeclaration  = 'operator' String ['*'|'-'] FormalParameters ';'
		                       DeclarationSequence [Body] 'end' String.

		Flags           		=  '{' [Identifier ['(' Expression ')'] {',' Identifier ['(' Expression ')'] }] '}'

		IdentifierDefinition = Identifier ['*'|'-'].

		FormalParameters     = '('[ParameterDeclaration {';' ParameterDeclaration}]')' [':' Type].

		ParameterDeclaration = ['var'|'const'] Identifier {',' Identifier}':' Type.

		Type                 = ArrayType | RecordType | PointerType | ObjectType | ProcedureType
		                       | EnumerationType | QualifiedIdentifier.

		ArrayType            = 'array' [Expression {',' Expression} | '[' MathArraySize {',' MathArraySize} ']' ] 'of' Type.

		MathArraySize        = Expression | '*' | '?'.

		RecordType           = 'record' ['(' QualifiedIdentifier ')']
		                       [VariableDeclaration {';' VariableDeclaration}] 'end'.

		PointerType          = 'pointer' [Flags] 'to' Type.

		ObjectType           = 'object' [Flags] ['(' (QualifiedIdentifier | ArrayType) ')'] DeclarationSequence [Body]
		                       'end' [Identifier]
		                     | 'object'.


		ProcedureType        = 'procedure' [Flags] [FormalParameters].

		EnumerationType		 = 'enum' Identifier {',' Identifier} 'end'.

		Body                 = 'begin' [Flags] StatementSequence ['finally' StatementSequence]
		                     | 'code' {any}.

		StatementSequence    = Statement {';' Statement}.

		Statement            =
		                     [
		                     Designator [':=' Expression]
		                     | 'if' Expression 'then' StatementSequence
		                        {'elsif' Expression 'then' StatementSequence} 'end'
		                     | 'with' Identifier ':' QualifiedIdentifier 'do'
		                         StatementSequence 'end'
		                     | 'case' Expression 'of' ['|'] Case {'|' Case} ['else' StatementSequence] 'end'
		                     | 'while' Expression 'do' StatementSequence 'end'
		                     | 'repeat' StatementSequence 'until' Expression
		                     | 'for' Identifier ':=' Expression 'to' Expression ['by' Expression] 'do'
		                         StatementSequence 'end'
		                     | 'loop' StatementSequence 'end'
		                     | 'exit'
		                     | 'return' [Expression]
		                     | 'await' Expression
		                     | 'begin' StatementBlock 'end'
		                     | 'code' {any} 'end'
		                     ].

		StatementBlock       = [Flags] StatementSequence.

		Case                 = RangeExpression {',' RangeExpression} ':' StatementSequence.

		Expression           = RangeExpression [RelationOp RangeExpression].

		RelationOp           = '=' | '.=' | '#' | '.#'
		                     | '<' | '.<' | '<=' | '.<=' | '>' | '.>' | '>=' | '.>='
		                     | 'in' | 'is'

		RangeExpression  = SimpleExpression | [SimpleExpression] '..' [SimpleExpression] ['by' SimpleExpression] | '*'.

		SimpleExpression     = ['+'|'-'] Term {AddOp Term}.

		AddOp                = '+' | '-' | 'or'.

		Term                 = Fcell {MulOp Fcell}.

		MulOp                = '*' | '**' | '.*' | '+*' | '/' | './' | 'div' | 'mod' | '&'.

		Fcell               = Number | Character | String | 'nil' | 'true' | 'false' | Set |
		                       '(' Expression ')' | '~' Fcell | Fcell '`' | Designator | MathArray.

		MathArray            = '[' Expression {',' Expression} ']'.

		Set                  = '{' [ RangeExpression {',' RangeExpression} ] '}'.

		Designator           = ('self' | Identifier)
		                       {'.' Identifier | '[' IndexList ']' | [Flags] '(' [ExpressionList] ')' | '^'}.

		IndexList            = '?' [',' ExpressionList ] | ExpressionList [',' '?'].

		ExpressionList       = Expression {','Expression}.

		VariableNameList     = IdentifierDefinition [Flags] {',' IdentifierDefinition [Flags]}.

		IdentifierDefinition = Identifier [ '*' | '-' ].

		QualifiedIdentifier  = Identifier ['.' Identifier].


		Identifier           = Letter {Letter | Digit | '_'}.

		Letter               = 'A' | 'B' | .. | 'Z' | 'a' | 'b' | .. | 'z'.

		String               = '"' {Character} '"' | "'" {Character} "'".

		Number               = Integer | Real.

		Integer              = Digit {Digit} | Digit {HexDigit} 'H'.

		Real                 = Digit {Digit} '.' {Digit} [ScaleFcell].

		ScaleFcell          = ('E' | 'D') ['+' | '-'] digit {digit}.

		HexDigit             = Digit | 'A' | 'B' | 'C' | 'D' | 'E' | 'F'

		Digit                = '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' .

	**)

TYPE
	Parser* = OBJECT
	VAR scanner: Scanner.Scanner;
		symbol-: Scanner.Symbol;
		diagnostics: Diagnostics.Diagnostics;
		currentScope: SyntaxTree.Scope;
		recentSymbol: SyntaxTree.Symbol;
		recentComment: SyntaxTree.Comment;
		moduleScope: SyntaxTree.ModuleScope;
		error-: BOOLEAN;
		activeCellsSupport: BOOLEAN;

		indent: LONGINT;   (* for debugging purposes only *)

		PROCEDURE S( CONST s: ARRAY OF CHAR );   (* for debugging purposes only *)
		VAR i: LONGINT;
		BEGIN
			D.Ln;  INC( indent );  D.Int( indent,1 );
			FOR i := 1 TO indent DO D.Str( "  " );  END;
			D.Str( "start: " );  D.Str( s );  D.Str( " at pos " );  D.Int( symbol.start,1 );
		END S;

		PROCEDURE E( CONST s: ARRAY OF CHAR );   (* for debugging purposes only *)
		VAR i: LONGINT;
		BEGIN
			D.Ln;  D.Int( indent,1 );
			FOR i := 1 TO indent DO D.Str( "  " );  END;
			D.Str( "end : " );  D.Str( s );  D.Str( " at pos " );  D.Int( symbol.start,1 );
		END E;

		PROCEDURE EE( CONST s, t: ARRAY OF CHAR );   (* for debugging purposes only *)
		VAR i: LONGINT;
		BEGIN
			D.Ln;  D.Int( indent,1 );
			FOR i := 1 TO indent DO D.Str( "  " );  END;
			D.Str( "end : " );  D.Str( s );  D.Str( " (" );  D.Str( t );  D.Str( ") at pos " );
		END EE;

		(** constructor, init parser with scanner providing input and with diagnostics for error output *)
		PROCEDURE & Init*( scanner: Scanner.Scanner; diagnostics: Diagnostics.Diagnostics );
		BEGIN
			SELF.scanner := scanner;
			SELF.diagnostics := diagnostics;
			error := ~scanner.GetNextSymbol(symbol);
			recentSymbol := NIL; recentComment := NIL;
			(* debugging *)
			indent := 0;
			activeCellsSupport := FALSE;
		END Init;

		PROCEDURE ActiveCellsSupport*;
		BEGIN activeCellsSupport := TRUE
		END ActiveCellsSupport;

		(** output error message and / or given code *)
		PROCEDURE Error(position: LONGINT; code: LONGINT; CONST message: ARRAY OF CHAR);
		VAR errorMessage: ARRAY 256 OF CHAR;
		BEGIN
			IF diagnostics # NIL THEN
				Basic.GetErrorMessage(code,message,errorMessage);
				diagnostics.Error(scanner.source, position, code, errorMessage);
			END;
			error := TRUE
		END Error;

		(** helper procedures interfacing to the scanner **)

		(** Get next symbol from scanner and store it in object-local variable 'symbol' *)
		PROCEDURE NextSymbol;
		VAR comment: SyntaxTree.Comment;
		BEGIN
			error := ~scanner.GetNextSymbol(symbol) OR error;
			WHILE ~error & (symbol.token = Scanner.Comment) DO
				comment := SyntaxTree.NewComment(symbol.start, currentScope, symbol.source^,symbol.stringLength);
				moduleScope.AddComment(comment);
				recentComment := comment; comment.SetPreviousSymbol(recentSymbol);
				error := ~scanner.GetNextSymbol(symbol);
			END;
		END NextSymbol;

		(** Check if current symbol equals sym. If yes then return true, return false otherwise *)
		PROCEDURE Peek(token: Scanner.Token): BOOLEAN;
		VAR comment: SyntaxTree.Comment;
		BEGIN
			WHILE ~error & (symbol.token = Scanner.Comment) DO
				comment := SyntaxTree.NewComment(symbol.start, currentScope, symbol.source^,symbol.stringLength);
				moduleScope.AddComment(comment);
				recentComment := comment; comment.SetPreviousSymbol(recentSymbol);
				error := ~scanner.GetNextSymbol(symbol);
			END;
			RETURN symbol.token = token
		END Peek;

		(** Check if the current symbol equals sym.If yes then read next symbol, report error otherwise. returns success value  *)
		PROCEDURE Mandatory( token: Scanner.Token): BOOLEAN;
		BEGIN
			ASSERT( token # Scanner.Identifier );  ASSERT( token # Scanner.String );  ASSERT( token # Scanner.Number );   (* because of NextSymbol ! *)
			IF ~Peek(token) THEN
				Error( symbol.start, token, "" );
				RETURN FALSE
			ELSE
				NextSymbol;
				RETURN TRUE
			END
		END Mandatory;

		(** Check if the current symbol equals sym. If yes then read next symbol, report error otherwise  *)
		PROCEDURE Check( token: Scanner.Token );
		VAR b: BOOLEAN;
		BEGIN
			b := Mandatory( token );
		END Check;

		(** Check if current symbol is an identifier. If yes then copy identifier to name and get next symbol,
		report error otherwise and set name to empty name. returns success value *)
		PROCEDURE MandatoryIdentifier( VAR name: Scanner.StringType): BOOLEAN;
		BEGIN
			IF Peek(Scanner.Identifier) THEN
				name := symbol.string;
				NextSymbol;
				RETURN TRUE
			ELSE
				Error( symbol.start, Scanner.Identifier, "" );
				name := "";
				RETURN FALSE
			END
		END MandatoryIdentifier;

		(** Expect an identifier (using MandatoryIdentifier) and return identifier object **)
		PROCEDURE Identifier(): SyntaxTree.Identifier;
		VAR position: LONGINT; name: Scanner.StringType; identifier: SyntaxTree.Identifier;
		BEGIN
			position := symbol.start;
			IF MandatoryIdentifier(name) THEN
				identifier := SyntaxTree.NewIdentifier(position,name);
			ELSE
				identifier := SyntaxTree.invalidIdentifier;
			END;
			RETURN identifier
		END Identifier;

		(** Check if current symbol is a string (or string-like character). If yes then copy identifier to name and get next symbol,
		report error otherwise and set name to empty name. returns success value*)
		PROCEDURE MandatoryString( VAR name: Scanner.StringType ): BOOLEAN;
		BEGIN
			IF Peek( Scanner.String) THEN
				name := symbol.string;
				NextSymbol;
				RETURN TRUE
			ELSIF Peek( Scanner.Character) THEN (* for compatibility with release: characters treated as strings *)
				name := symbol.string;
				NextSymbol;
				RETURN TRUE
			ELSE
				Error( symbol.start, Scanner.String, "" );
				name := "";
				RETURN FALSE
			END
		END MandatoryString;

		(** Check if current symbol is an identifier and if the name matches. If yes then get next symbol, report error otherwise. returns success value*)
		PROCEDURE ExpectThisIdentifier( name: SyntaxTree.Identifier ): BOOLEAN;
		VAR string: ARRAY 64 OF CHAR;
		BEGIN
			IF name = NIL THEN (* nothing to be expected *)
				RETURN TRUE
			ELSIF (symbol.token # Scanner.Identifier) OR (Basic.MakeString(symbol.string) #  name.name) THEN
				Basic.GetString(name.name,string);
				Error( symbol.start, Scanner.Identifier, string );
				RETURN FALSE
			ELSE
				NextSymbol;
				RETURN TRUE
			END
		END ExpectThisIdentifier;

		(** Check if current symbol is an identifier and if the name matches. If yes then get next symbol, report error otherwise. returns success value*)
		PROCEDURE ExpectThisString( CONST name: ARRAY OF CHAR ): BOOLEAN;
		BEGIN
			IF (Peek(Scanner.String) OR Peek(Scanner.Character) OR Peek(Scanner.Identifier)) & (symbol.string = name) THEN
				NextSymbol;
				RETURN TRUE
			ELSE
				Error( symbol.start, Scanner.String, name );
				RETURN FALSE
			END
		END ExpectThisString;

		(** Check if current symbol equals sym. If yes then get next symbol, return false otherwise *)
		PROCEDURE Optional( token: Scanner.Token ): BOOLEAN;
		BEGIN
			(* do not use for Identifier, String or Number, if the result is needed ! *)
			IF Peek(token) THEN
				NextSymbol;
				RETURN TRUE
			ELSE
				RETURN FALSE
			END
		END Optional;

		(* ignore one ore more symbols of type token *)
		PROCEDURE Ignore(token: Scanner.Token);
		BEGIN WHILE Optional(token) DO END;
		END Ignore;

		(** Parsing according to the EBNF **)

		(** QualifiedIdentifier = Identifier ['.' Identifier]. **)
		PROCEDURE QualifiedIdentifier( ): SyntaxTree.QualifiedIdentifier;
		VAR prefix,suffix: SyntaxTree.Identifier; qualifiedIdentifier: SyntaxTree.QualifiedIdentifier;  position: LONGINT;
		BEGIN
			IF Trace THEN S( "QualifiedIdentifier" ) END;
			position:= symbol.start;
			prefix := Identifier();
			IF prefix # SyntaxTree.invalidIdentifier THEN
				IF ~Optional( Scanner.Period )THEN
					suffix := prefix;  prefix := NIL;   (* empty *)
				ELSE
					 suffix := Identifier();
				END;
				qualifiedIdentifier := SyntaxTree.NewQualifiedIdentifier( position, prefix,suffix);
			ELSE
				qualifiedIdentifier := SyntaxTree.invalidQualifiedIdentifier;
			END;
			IF Trace THEN E( "QualifiedIdentifier" ) END;
			RETURN qualifiedIdentifier
		END QualifiedIdentifier;

		(** IdentifierDefinition = Identifier [ '*' | '-' ].  **)
		PROCEDURE IdentifierDefinition( VAR name: SyntaxTree.Identifier;  VAR access: SET; allowedReadOnly: BOOLEAN);
		BEGIN
			IF Trace THEN S( "IdentifierDefinition" ) END;
			name := Identifier();

			IF Optional( Scanner.Times ) THEN
				access := SyntaxTree.Public + SyntaxTree.Protected + SyntaxTree.Internal;
			ELSIF Optional( Scanner.Minus ) THEN
				IF ~allowedReadOnly THEN
					Error( symbol.start, Diagnostics.Invalid, "may not be defined read-only" )
				ELSE
					access :=  SyntaxTree.ReadOnly + {SyntaxTree.InternalWrite};
				END;
			ELSE
				access := SyntaxTree.Internal;
			END;
			IF Trace THEN E( "IdentifierDefinition") END;
		END IdentifierDefinition;

		(** ExpressionList = Expression { ',' Expression }.  **)
		PROCEDURE ExpressionList( expressionList: SyntaxTree.ExpressionList );
		VAR expression: SyntaxTree.Expression;
		BEGIN
			IF Trace THEN S( "ExpressionList" ) END;
			REPEAT
				expression := Expression();
				expressionList.AddExpression( expression )
			UNTIL ~Optional( Scanner.Comma );
			IF Trace THEN E( "ExpressionList" ) END;
		END ExpressionList;

		(** IndexList = '?' [',' ExpressionList ] | ExpressionList [',' '?']. **)
		PROCEDURE IndexList(expressionList: SyntaxTree.ExpressionList);
		VAR
			position: LONGINT;
			done: BOOLEAN;
		BEGIN
			IF Trace THEN S( "IndexList" ) END;
			position := symbol.start;

			IF Optional(Scanner.Questionmark) THEN
				expressionList.AddExpression(SyntaxTree.NewTensorRangeExpression(position));
				WHILE Optional(Scanner.Comma) DO
					expressionList.AddExpression(Expression())
				END
			ELSE
				expressionList.AddExpression(Expression());

				done := FALSE;
				WHILE ~done DO
					IF Optional(Scanner.Comma) THEN
						IF Optional(Scanner.Questionmark) THEN
							expressionList.AddExpression(SyntaxTree.NewTensorRangeExpression(position));
							done := TRUE;
						ELSE
							expressionList.AddExpression(Expression())
						END

					ELSE
						done := TRUE
					END
				END
			END;
			IF Trace THEN E( "IndexList" ) END;
		END IndexList;

		(** RangeExpression = SimpleExpression | [SimpleExpression] '..' [SimpleExpression] ['by' SimpleExpression] | '*'.
			i.e., a RangeExpression can have one of the following forms:
				'*'
				'..' [delimiter]
				'..' 'by' SimpleExpression
				'..' SimpleExpression
				'..' SimpleExpression 'by' SimpleExpression
				SimpleExpression
				SimpleExpression '..' [delimiter]
				SimpleExpression '..' 'by' SimpleExpression
				SimpleExpression '..' SimpleExpression
				SimpleExpression '..' SimpleExpression 'by' SimpleExpression

			a RangeExpression is always delimited by any of the following tokens: ",", ";", ":", "]", ")", "}", "=", "#", "END".
		**)
		PROCEDURE RangeExpression(): SyntaxTree.Expression;
		VAR
			expression, first, last, step: SyntaxTree.Expression;
			position: LONGINT;

			PROCEDURE HasDelimiter(): BOOLEAN;
			BEGIN RETURN
						Peek(Scanner.Comma) OR Peek(Scanner.Semicolon) OR Peek(Scanner.Colon) OR
						Peek(Scanner.RightBracket) OR Peek(Scanner.RightParenthesis) OR Peek(Scanner.RightBrace) OR
						Peek(Scanner.Equal) OR Peek(Scanner.Unequal) OR Peek(Scanner.End)
			END HasDelimiter;

		BEGIN
			IF Trace THEN S( "RangeExpression" ) END;
			position := symbol.start;

			IF Optional(Scanner.Times) THEN
				expression := SyntaxTree.NewRangeExpression(position, NIL, NIL, NIL)

			ELSIF Optional(Scanner.Upto) THEN
				(* is range expression *)
				first := NIL;
				IF HasDelimiter() THEN
					last := NIL;
					step := NIL
				ELSIF Optional(Scanner.By) THEN
					last := NIL;
					step := SimpleExpression()
				ELSE
					last := SimpleExpression();
					IF Optional(Scanner.By) THEN
						step := SimpleExpression()
					ELSE
						step := NIL
					END
				END;
				expression := SyntaxTree.NewRangeExpression(position, first, last, step)
			ELSE
				expression := SimpleExpression();
				IF Optional(Scanner.Upto) THEN
					(* is range expression *)
					first := expression;

					IF HasDelimiter() THEN
						last := NIL;
						step := NIL
					ELSIF Optional(Scanner.By) THEN
						last := NIL;
						step := SimpleExpression()
					ELSE
						last := SimpleExpression();
						IF Optional(Scanner.By) THEN
							step := SimpleExpression()
						ELSE
							step := NIL
						END
					END;
					expression := SyntaxTree.NewRangeExpression(position, first, last, step)
				END;
			END;

			IF Trace THEN E( "RangeExpression" ) END;
			RETURN expression
		END RangeExpression;

		(** Designator  = ('self' | 'result' | Identifier [Flags])
		                  {'.' Identifier  [Flags] | '[' IndexList ']' | '(' [ExpressionList] ')' | '^'}.
		**)
		PROCEDURE Designator( ): SyntaxTree.Designator;
		VAR
			designator: SyntaxTree.Designator;  expressionList: SyntaxTree.ExpressionList;
			identifier: SyntaxTree.Identifier; position: LONGINT;
			modifier: SyntaxTree.Modifier;
		BEGIN
			IF Trace THEN S( "Designator" ) END;
			position := symbol.start;
			IF Optional(Scanner.Self) THEN
				designator := SyntaxTree.NewSelfDesignator(position);
			ELSIF Optional(Scanner.Result) THEN
				designator := SyntaxTree.NewResultDesignator(position);
			ELSE
				identifier := Identifier();
				designator := SyntaxTree.NewIdentifierDesignator(identifier.position,identifier);
			END;

			LOOP
				position := symbol.start;
				IF Optional( Scanner.LeftParenthesis ) THEN
					expressionList := SyntaxTree.NewExpressionList();
					IF ~Optional( Scanner.RightParenthesis ) THEN
						ExpressionList( expressionList );
						Check( Scanner.RightParenthesis )
					END;
					designator := SyntaxTree.NewParameterDesignator( position,designator,expressionList);
				ELSIF Optional( Scanner.Period ) THEN
					identifier := Identifier();
					designator := SyntaxTree.NewSelectorDesignator(identifier.position,designator,identifier);
				ELSIF Optional( Scanner.LeftBracket ) THEN
					expressionList := SyntaxTree.NewExpressionList();
					IndexList( expressionList );
					Check( Scanner.RightBracket );
					designator:= SyntaxTree.NewBracketDesignator( position,designator,expressionList );
				ELSIF Optional( Scanner.Arrow ) THEN
					designator:= SyntaxTree.NewArrowDesignator( position,designator );
				ELSE EXIT
				END;
			END;
			IF Trace THEN E( "Designator" ) END;
			RETURN designator
		END Designator;

		(** Set = '{' [ Expression {',' Expression} ] '}'. **)
		PROCEDURE Set( ): SyntaxTree.Expression;
		VAR
			set: SyntaxTree.Set;
		BEGIN
			IF Trace THEN S( "Set" ) END;

			set := SyntaxTree.NewSet(symbol.start);
			Check(Scanner.LeftBrace);
			IF ~Optional(Scanner.RightBrace) THEN
				REPEAT
					set.elements.AddExpression(RangeExpression())
				UNTIL ~Optional(Scanner.Comma);
				Check(Scanner.RightBrace);
			END;
			set.End(symbol.start);

			IF Trace THEN E( "Set" ) END;
			RETURN set
		END Set;

		(* MathArray = '[' Expression {',' Expression} ']'. *)
		PROCEDURE MathArray(): SyntaxTree.Expression;
		VAR array: SyntaxTree.MathArrayExpression; element: SyntaxTree.Expression;
		BEGIN
			array := SyntaxTree.NewMathArrayExpression(symbol.start);
			IF ~Optional(Scanner.RightBracket) THEN
				REPEAT
					element := Expression();
					array.elements.AddExpression(element);
				UNTIL ~Optional(Scanner.Comma);
				Check(Scanner.RightBracket);
			END;
			RETURN array
		END MathArray;

		(** Fcell = Number | Character | String | 'nil' | 'true' | 'false' | Set
			 			  | '(' Expression ')' | '~' Fcell | Fcell '`' | Designator | MathArray.**)
		PROCEDURE Fcell( ): SyntaxTree.Expression;
		VAR fcell: SyntaxTree.Expression; position: LONGINT;
		BEGIN
			IF Trace THEN S( "Fcell" ) END;
			position := symbol.start;
			CASE symbol.token OF
			| Scanner.Number:
					IF (symbol.numberType = Scanner.Integer) THEN
						fcell := SyntaxTree.NewIntegerValue( position, symbol.integer);
						fcell.End( symbol.end );
					ELSIF (symbol.numberType = Scanner.Hugeint) THEN
						fcell := SyntaxTree.NewIntegerValue(position, symbol.hugeint);
						fcell.End( symbol.end );
					ELSIF (symbol.numberType = Scanner.Real) OR (symbol.numberType = Scanner.Longreal) THEN
						fcell := SyntaxTree.NewRealValue( position, symbol.real);
						fcell(SyntaxTree.RealValue).SetSubtype(symbol.numberType);
						fcell.End( symbol.end );
					ELSE HALT( 100 )
					END;
					NextSymbol;
			| Scanner.Character:
					fcell := SyntaxTree.NewCharacterValue(position,symbol.character);
					fcell.End(symbol.end);
					NextSymbol;
			| Scanner.String:
					fcell := SyntaxTree.NewStringValue( position, symbol.string );
					fcell.End( symbol.end );
					NextSymbol;
			| Scanner.Nil:
					fcell := SyntaxTree.NewNilValue( position );
					fcell.End( symbol.end );
					NextSymbol;
			| Scanner.True:
					fcell := SyntaxTree.NewBooleanValue( position, TRUE );
					fcell.End( symbol.end );
					NextSymbol;
			| Scanner.False:
					fcell := SyntaxTree.NewBooleanValue( position, FALSE );
					fcell.End( symbol.end );
					NextSymbol;
			| Scanner.LeftBrace:
					fcell := Set();
			| Scanner.LeftParenthesis:
					NextSymbol;
					fcell := Expression();
					Check( Scanner.RightParenthesis );
					fcell.End( symbol.end );
			| Scanner.Not:
					NextSymbol;
					fcell := Fcell();
					fcell := SyntaxTree.NewUnaryExpression( position, fcell, Scanner.Not );
					fcell.End( symbol.end );
			| Scanner.Self, Scanner.Result, Scanner.Identifier:
					fcell := Designator();
					fcell.End( symbol.end );
			| Scanner.LeftBracket:
					NextSymbol;
					fcell := MathArray();
					fcell.End(symbol.end);
			ELSE
				Error( position, Basic.ValueStartIncorrectSymbol, "" );
				NextSymbol;  fcell := SyntaxTree.invalidExpression;
			END;
			(* suffix *)
			IF Optional(Scanner.Transpose) THEN
				IF (fcell IS SyntaxTree.UnaryExpression) & (fcell(SyntaxTree.UnaryExpression).operator = Scanner.Transpose) THEN
					(* transpose operator has higher precedence than not, reevaluate expression: *)
					fcell := fcell(SyntaxTree.UnaryExpression).left;
					fcell := SyntaxTree.NewUnaryExpression(position,fcell,Scanner.Transpose);
					fcell := SyntaxTree.NewUnaryExpression(position,fcell,Scanner.Not);
				ELSE
					fcell := SyntaxTree.NewUnaryExpression(position,fcell,Scanner.Transpose);
				END;
			END;
			IF Trace THEN E( "Fcell" ) END;
			RETURN fcell
		END Fcell;

		(** Term = Fcell {MulOp Fcell}.
		   MulOp = '*' | '**' | '.*' | '+*' | '/' | './' | 'div' | 'mod' | '&'.
		**)
		PROCEDURE Term( ): SyntaxTree.Expression;
		VAR term, fcell: SyntaxTree.Expression;  operator: LONGINT; position: LONGINT;
		BEGIN
			IF Trace THEN S( "Term" ) END;
			position := symbol.start;
			term := Fcell();
			WHILE (symbol.token >= Scanner.Times) & (symbol.token <= Scanner.And) DO
				operator := symbol.token;
				NextSymbol;
				fcell := Fcell();
				term := SyntaxTree.NewBinaryExpression( position, term, fcell, operator );
			END;
			term.End( symbol.end );
			IF Trace THEN E( "Term" ) END;
			RETURN term
		END Term;

		(** SimpleExpression     = ['+'|'-'] Term {AddOp Term}.
			AddOp                = '+' | '-' | 'or'.
		**)
		PROCEDURE SimpleExpression( ): SyntaxTree.Expression;
		VAR operator: LONGINT;  term, expression: SyntaxTree.Expression;  position: LONGINT;
		BEGIN
			IF Trace THEN S( "SimpleExpression" ) END;
			position := symbol.start;
			IF Peek(Scanner.Plus) OR Peek(Scanner.Minus) THEN (* sign should be part of the fcell *)
				operator := symbol.token;
				NextSymbol;
				term := Term();
				expression := SyntaxTree.NewUnaryExpression( position, term, operator );
			ELSE expression := Term();
			END;
			WHILE (symbol.token >= Scanner.Or) & (symbol.token <= Scanner.Minus) DO
				operator := symbol.token;
				NextSymbol;
				term := Term();
				expression := SyntaxTree.NewBinaryExpression( position, expression, term, operator );
			END;
			IF Trace THEN E( "SimpleExpression" ) END;
			RETURN expression
		END SimpleExpression;

		(**
			Expression           = RangeExpression [RelationOp RangeExpression].
			RelationOp           = '=' | '.=' | '#' | '.#'
			                     | '<' | '.<' | '<=' | '.<=' | '>' | '.>' | '>=' | '.>='
			                     | 'in' | 'is'
		**)
		PROCEDURE Expression( ): SyntaxTree.Expression;
		VAR expression, rightExpression: SyntaxTree.Expression;  operator: LONGINT;  position: LONGINT;
		BEGIN
			IF Trace THEN S( "Expression" ) END;
			position := symbol.start;
			expression := RangeExpression();
			IF (symbol.token >= Scanner.Equal) & (symbol.token <= Scanner.Is) THEN
				operator := symbol.token;
				NextSymbol;
				rightExpression := RangeExpression();
				expression := SyntaxTree.NewBinaryExpression(position, expression, rightExpression, operator );
			END;
			IF Trace THEN E( "Expression" ) END;
			RETURN expression
		END Expression;

		(** Case = RangeExpression {',' RangeExpression} ':' StatementSequence. **)
		PROCEDURE Case( caseStatement: SyntaxTree.CaseStatement );
		VAR
			casePart: SyntaxTree.CasePart;
			statements: SyntaxTree.StatementSequence;
			element: SyntaxTree.Expression;
		BEGIN
			IF Trace THEN S( "Case" ) END;
			casePart := SyntaxTree.NewCasePart();
			REPEAT
				element := RangeExpression();
				casePart.elements.AddExpression( element );
			UNTIL ~Optional( Scanner.Comma );
			Check( Scanner.Colon );
			statements := StatementSequence(caseStatement);
			casePart.SetStatements( statements );
			caseStatement.AddCasePart( casePart );
			IF Trace THEN E( "Case" ) END;
		END Case;


		(**		Statement =
                     [
                     Designator [':=' Expression]
                     | 'if' Expression 'then' StatementSequence
                        {'elsif' Expression 'then' StatementSequence} 'end'
                     | 'with' Identifier ':' QualifiedIdentifier 'do'
                         StatementSequence 'end'
                     | 'case' Expression 'of' ['|'] Case {'|' Case} ['else' StatementSequence] 'end'
                     | 'while' Expression 'do' StatementSequence 'end'
                     | 'repeat' StatementSequence 'until' Expression
                     | 'for' Identifier ':=' Expression 'to' Expression ['by' Expression] 'do'
                         StatementSequence 'end'
                     | 'loop' StatementSequence 'end'
                     | 'exit'
                     | 'return' [Expression]
                     | 'await' Expression
                     | 'begin' StatementBlock 'end'
                     | 'code' {any} 'end'
                     ].
		**)
		PROCEDURE Statement( statements: SyntaxTree.StatementSequence; outer: SyntaxTree.Statement): BOOLEAN;
		VAR qualifiedIdentifier: SyntaxTree.QualifiedIdentifier;  expression: SyntaxTree.Expression; designator: SyntaxTree.Designator;  statement: SyntaxTree.Statement;
			ifStatement: SyntaxTree.IfStatement; elsifPart: SyntaxTree.IfPart;   statementSequence: SyntaxTree.StatementSequence;  withStatement: SyntaxTree.WithStatement;
			withPart: SyntaxTree.WithPart; caller: SyntaxTree.ProcedureCallStatement;
			caseStatement: SyntaxTree.CaseStatement;  whileStatement: SyntaxTree.WhileStatement;  repeatStatement: SyntaxTree.RepeatStatement;  forStatement: SyntaxTree.ForStatement;
			identifier: SyntaxTree.Identifier;  loopStatement: SyntaxTree.LoopStatement;  returnStatement: SyntaxTree.ReturnStatement;  awaitStatement: SyntaxTree.AwaitStatement;
			qualifiedType: SyntaxTree.QualifiedType; code : SyntaxTree.Code; position: LONGINT; result: BOOLEAN;
			modifier: SyntaxTree.Modifier;
		BEGIN
			IF Trace THEN S( "Statement" ) END;
			CASE symbol.token OF
			| Scanner.Identifier, Scanner.Self, Scanner.Result:
					designator := Designator();
					position := symbol.start;
					IF Optional( Scanner.Becomes ) THEN
						expression := Expression();
						statement := SyntaxTree.NewAssignment( position, designator, expression,outer )
					ELSE
						caller := SyntaxTree.NewProcedureCallStatement(designator.position, designator,outer);
						statement := caller;
					END;
					statements.AddStatement( statement );
					result := TRUE
			| Scanner.If:
					NextSymbol;
					ifStatement := SyntaxTree.NewIfStatement( symbol.start ,outer);
					expression := Expression();
					ifStatement.ifPart.SetCondition( expression );
					Check( Scanner.Then );
					statementSequence := StatementSequence(ifStatement);
					ifStatement.ifPart.SetStatements( statementSequence );
					WHILE Optional( Scanner.Elsif ) DO
						elsifPart := SyntaxTree.NewIfPart();
						ifStatement.AddElsifPart( elsifPart);
						expression := Expression();
						elsifPart.SetCondition( expression );
						Check( Scanner.Then );
						statementSequence := StatementSequence(ifStatement);
						elsifPart.SetStatements( statementSequence );
					END;
					IF Optional( Scanner.Else ) THEN
						statementSequence := StatementSequence(ifStatement);
						ifStatement.SetElsePart( statementSequence );
					END;
					Check( Scanner.End );  statements.AddStatement( ifStatement );
					result := TRUE
			| Scanner.With:
					withStatement := SyntaxTree.NewWithStatement( symbol.start ,outer);
					NextSymbol;
					REPEAT
						identifier := Identifier();
						IF Optional(Scanner.Period) & Optional(Scanner.Identifier) THEN
							Error(identifier.position,Diagnostics.Invalid,"forbidden qualified identifier in with statement");
						END;
						withPart := SyntaxTree.NewWithPart();
						withStatement.AddWithPart(withPart);
						designator := SyntaxTree.NewIdentifierDesignator(identifier.position,identifier);
						withPart.SetVariable( designator );
						Check( Scanner.Colon );
						qualifiedIdentifier := QualifiedIdentifier();
						qualifiedType := SyntaxTree.NewQualifiedType(qualifiedIdentifier.suffix.position, currentScope, qualifiedIdentifier);
						withPart.SetType(qualifiedType);
						Check( Scanner.Do );
						statementSequence := StatementSequence(withStatement);
						withPart.SetStatements( statementSequence );
					UNTIL ~Optional(Scanner.Bar) OR ~CascadedWithSupport;
					IF CascadedWithSupport & Optional(Scanner.Else) THEN
						statementSequence := StatementSequence(withStatement);
						withStatement.SetElsePart(statementSequence);
					END;
					Check( Scanner.End );
					statements.AddStatement( withStatement );
					result := TRUE
			| Scanner.Case:
					caseStatement := SyntaxTree.NewCaseStatement( symbol.start,outer );
					NextSymbol;
					expression := Expression();
					Check( Scanner.Of );
					caseStatement.SetVariable( expression );
					IF Optional(Scanner.Bar) THEN END;
					REPEAT
						Case(caseStatement)
					UNTIL ~Optional(Scanner.Bar);
					IF Optional( Scanner.Else ) THEN
						statementSequence := StatementSequence(caseStatement);
						caseStatement.SetElsePart( statementSequence );
					END;
					Check( Scanner.End );
					statements.AddStatement( caseStatement );
					result := TRUE
			| Scanner.While:
					NextSymbol;
					whileStatement := SyntaxTree.NewWhileStatement( symbol.start, outer );
					expression := Expression();
					Check( Scanner.Do );
					whileStatement.SetCondition( expression );
					statementSequence := StatementSequence(whileStatement);
					whileStatement.SetStatements( statementSequence );
					Check( Scanner.End );
					statements.AddStatement( whileStatement );
					result := TRUE
			| Scanner.Repeat:
					NextSymbol;
					repeatStatement := SyntaxTree.NewRepeatStatement( symbol.start, outer );
					statementSequence := StatementSequence(repeatStatement);
					repeatStatement.SetStatements( statementSequence );
					Check( Scanner.Until );
					expression := Expression();
					repeatStatement.SetCondition( expression );
					statements.AddStatement( repeatStatement );
					result := TRUE
			| Scanner.For:
					NextSymbol;
					forStatement := SyntaxTree.NewForStatement( symbol.start, outer);
					identifier := Identifier();
					IF Optional(Scanner.Period) & Optional(Scanner.Identifier) THEN
						Error(identifier.position,Diagnostics.Invalid,"forbidden non-local counter variable");
					END;
					designator := SyntaxTree.NewIdentifierDesignator(identifier.position,identifier);
					forStatement.SetVariable( designator );
					Check( Scanner.Becomes );
					expression := Expression();
					forStatement.SetFrom( expression );
					Check( Scanner.To );
					expression := Expression();
					forStatement.SetTo( expression );
					IF Optional( Scanner.By ) THEN
						expression := Expression();
						forStatement.SetBy( expression );
					END;
					Check( Scanner.Do );
					statementSequence := StatementSequence(forStatement);
					forStatement.SetStatements( statementSequence );
					Check( Scanner.End );
					statements.AddStatement( forStatement );
					result := TRUE
			| Scanner.Loop:
					NextSymbol;
					loopStatement := SyntaxTree.NewLoopStatement( symbol.start ,outer);
					statementSequence := StatementSequence(loopStatement);
					loopStatement.SetStatements( statementSequence );
					Check( Scanner.End );
					statements.AddStatement( loopStatement );
					result := TRUE;
			| Scanner.Exit:
					NextSymbol;
					statement := SyntaxTree.NewExitStatement( symbol.start, outer);
					statements.AddStatement( statement );
					result := TRUE;
			| Scanner.Return:
					NextSymbol;
					returnStatement := SyntaxTree.NewReturnStatement( symbol.start, outer);
					IF (symbol.token >= Scanner.Plus) & (symbol.token <= Scanner.Identifier) THEN
						expression := Expression();
						returnStatement.SetReturnValue( expression );
					END;
					statements.AddStatement( returnStatement );
					result := TRUE;
			| Scanner.Begin:
					NextSymbol;  statement := StatementBlock(outer);  statements.AddStatement( statement );  Check( Scanner.End );
					result := TRUE;
			| Scanner.Await:
					awaitStatement := SyntaxTree.NewAwaitStatement( symbol.start, outer );
					NextSymbol;
					expression := Expression();
					awaitStatement.SetCondition( expression );
					statements.AddStatement( awaitStatement );
					result := TRUE
			| Scanner.Code:
				(* assemble *)
				code := Code(outer);
				Check(Scanner.End);
				statements.AddStatement( code );
				result := TRUE
			| Scanner.End:  result := FALSE (* end of if, with, case, while, for, loop, or statement sequence *)
			| Scanner.Until: result := FALSE  (* end of repeat *)
			| Scanner.Else:  result := FALSE (* else of if or case *)
			| Scanner.Elsif:  result := FALSE (* elsif of if *)
			| Scanner.Bar:  result := FALSE (* next case *)
			| Scanner.Finally: result := FALSE  (* end block by finally statement *)
			| Scanner.Semicolon: result := FALSE (* allow the empty statement *)
			(* builtin pseudo procedures are resolved by checker *)
			ELSE Error( symbol.start, Scanner.Semicolon, "" ); result := FALSE;
			END;
			IF Trace THEN E( "Statement" ) END;
			RETURN result
		END Statement;

		(** StatementSequence = Statement {';' Statement}. **)
		PROCEDURE StatementSequence(outer: SyntaxTree.Statement ): SyntaxTree.StatementSequence;
		VAR statements: SyntaxTree.StatementSequence; b: BOOLEAN;
		BEGIN
			IF Trace THEN S( "StatementSequence" ) END;
			statements := SyntaxTree.NewStatementSequence();
			IF Lax THEN
				WHILE ~Peek(Scanner.Return) & Statement(statements,outer) DO Ignore(Scanner.Semicolon) END;
				IF Peek(Scanner.Return) & Statement(statements,outer) THEN Ignore(Scanner.Semicolon) END; (* return bound to end of statement sequence *)
			ELSE
				REPEAT
					b := Statement( statements,outer )
				UNTIL ~Optional( Scanner.Semicolon );
			END;
			IF Trace THEN E( "StatementSequence" ) END;
			RETURN statements
		END StatementSequence;

		(** StatementBlock = ['{' BlockModifier '}'] StatementSequence. **)
		PROCEDURE StatementBlock(outer: SyntaxTree.Statement): SyntaxTree.StatementBlock;
		VAR block: SyntaxTree.StatementBlock;
		BEGIN
			IF Trace THEN S( "StatementBlock" ) END;
			block := SyntaxTree.NewStatementBlock( symbol.end, outer );
			IF Optional( Scanner.LeftBrace ) THEN
				block.SetModifier(Flags());
			END;
			block.SetStatementSequence( StatementSequence(block) );
			IF Trace THEN E( "StatementBlock" ) END;
			RETURN block
		END StatementBlock;

		(** Code = {  Any \ 'end' } . **)
		PROCEDURE Code(outer: SyntaxTree.Statement): SyntaxTree.Code;
		VAR startPos, endPos, i ,len: LONGINT; codeString: Scanner.SourceString; code: SyntaxTree.Code;
		BEGIN
			startPos := symbol.start;
			IF scanner.SkipToNextEnd(startPos, endPos, symbol) THEN
				codeString := symbol.source;
				code := SyntaxTree.NewCode(startPos,outer);
				i := 0; len := LEN(codeString);
				code.SetSourceCode(codeString,len);
			END;
			RETURN code;
		END Code;

		(** Body = 'begin' ['{' BlockModifier '}'] StatementSequence ['finally' StatementSequence]
		         | 'code' Code. **)
		PROCEDURE Body( scope: SyntaxTree.ProcedureScope ): SyntaxTree.Body;
		VAR body: SyntaxTree.Body; code: SyntaxTree.Code; position: LONGINT;  previousScope: SyntaxTree.Scope;
		BEGIN
			previousScope := currentScope;
			currentScope := scope;
			IF Trace THEN S( "Body" ) END;
			IF Peek( Scanner.Code ) THEN
				body := SyntaxTree.NewBody(symbol.start,scope); (* empty body for the time being *)
				(* assemble *)
				code := Code(body);
				body.SetCode(code);
			ELSIF Mandatory( Scanner.Begin ) THEN
				body := SyntaxTree.NewBody(symbol.start,scope);
				IF Optional( Scanner.LeftBrace ) THEN
					body.SetModifier(Flags());
				END;
				position := symbol.start;
				body.SetStatementSequence(StatementSequence(body));
				IF Optional( Scanner.Finally ) THEN
					body.SetFinally(StatementSequence(body));
				END;
			END;
			IF Trace THEN E( "Body" ) END;
			currentScope := previousScope;
			RETURN body
		END Body;

		(** wrapper for a body in records and modules *)
		PROCEDURE BodyProcedure(parentScope: SyntaxTree.Scope): SyntaxTree.Procedure;
		VAR procedureScope: SyntaxTree.ProcedureScope; procedure: SyntaxTree.Procedure;
		BEGIN
			procedureScope := SyntaxTree.NewProcedureScope(parentScope);
			IF parentScope IS SyntaxTree.ModuleScope THEN
				procedure := SyntaxTree.NewProcedure( symbol.start, Global.ModuleBodyName,procedureScope);
				procedure.SetAccess(SyntaxTree.Hidden);
			ELSE
				procedure := SyntaxTree.NewProcedure( symbol.start, Global.RecordBodyName,procedureScope);
				(*! todo: make this a hidden symbol. Problematic when used with paco. *)
				procedure.SetAccess(SyntaxTree.Public + SyntaxTree.Protected + SyntaxTree.Internal);
			END;
			parentScope.AddProcedure(procedure);
			procedure.SetType(SyntaxTree.NewProcedureType(-1,parentScope));
			procedure.SetBodyProcedure(TRUE);
			procedureScope.SetBody(Body(procedureScope));
			RETURN procedure
		END BodyProcedure;

		(* ProcedureType = 'procedure' [Flags] [FormalParameters]. *)
		PROCEDURE ProcedureType(position: LONGINT;  parentScope: SyntaxTree.Scope): SyntaxTree.ProcedureType;
		VAR procedureType: SyntaxTree.ProcedureType;
		BEGIN
			IF Trace THEN S( "ProcedureType" ) END;
			(* procedure symbol already consumed *)
			procedureType := SyntaxTree.NewProcedureType( position, parentScope);
			IF Optional(Scanner.LeftBrace) THEN
				procedureType.SetModifiers(Flags());
			END;
			IF Optional(Scanner.LeftParenthesis) THEN FormalParameters( procedureType, parentScope) END;
			IF Trace THEN E( "ProcedureType" )
			END;
			RETURN procedureType;
		END ProcedureType;

		(** ObjectType = 'object' ['(' (QualifiedIdentifier | ArrayType) ')'] DeclarationSequence [Body] 'end' [Identifier] | 'object'. **)
		PROCEDURE ObjectType(position: LONGINT;  name: SyntaxTree.Identifier; parentScope: SyntaxTree.Scope ): SyntaxTree.Type;
		VAR
			objectType: SyntaxTree.RecordType;
			pointerType: SyntaxTree.PointerType;
			recordScope: SyntaxTree.RecordScope;
			qualifiedIdentifier: SyntaxTree.QualifiedIdentifier;
			baseType: SyntaxTree.Type;
			identifier: SyntaxTree.Identifier;
			str: Scanner.StringType;
			type: SyntaxTree.Type;
			modifiers: SyntaxTree.Modifier;
		BEGIN
			IF Trace THEN S( "ObjectType" ) END;
			(* symbol object already consumed *)

			(* generic empty OBJECT type *)
			IF Peek(Scanner.Semicolon) OR Peek(Scanner.RightParenthesis) THEN
				Scanner.GetKeyword(scanner.case,Scanner.Object,str);
				identifier := SyntaxTree.NewIdentifier(position,str);
	      		qualifiedIdentifier := SyntaxTree.NewQualifiedIdentifier(position,NIL,identifier);
				type := SyntaxTree.NewQualifiedType( position, parentScope, qualifiedIdentifier );
				RETURN type
			END;
			recordScope := SyntaxTree.NewRecordScope(parentScope);
			pointerType := SyntaxTree.NewPointerType(position,parentScope);
			objectType := SyntaxTree.NewRecordType( position,parentScope,recordScope);
			objectType.IsObject(TRUE);
			objectType.SetPointerType(pointerType);

			pointerType.SetPointerBase(objectType);

			IF Optional(Scanner.LeftBrace) THEN
				modifiers := Flags();
				pointerType.SetModifiers(modifiers);
			END;

			IF Optional( Scanner.LeftParenthesis ) THEN
				IF Optional(Scanner.Array) THEN
					baseType := ArrayType(position, parentScope) (* TODO: correct position? *)
				ELSE
					qualifiedIdentifier := QualifiedIdentifier();
					baseType := SyntaxTree.NewQualifiedType(qualifiedIdentifier.suffix.position, parentScope, qualifiedIdentifier)
				END;
				objectType.SetBaseType(baseType);
				Check( Scanner.RightParenthesis )
			END;
			(*
			IF Optional( Scanner.Implements ) THEN
				REPEAT
					qualifiedIdentifier := QualifiedIdentifier()
				UNTIL ~Optional( Scanner.Comma );
			END;
			*)

			IF Optional( Scanner.Semicolon ) THEN
				(*Warning(symbol.start,Diagnostics.Invalid,"no semicolon allowed here");*)
			END;

			DeclarationSequence( recordScope);
			IF Peek(Scanner.Begin) OR Peek(Scanner.Code) THEN
				recordScope.SetBodyProcedure(BodyProcedure(recordScope));
			END;
			Check(Scanner.End);

			IF ExpectThisIdentifier( name ) THEN
				(* check name not always, reflect in EBNF? *)
			END;
			IF Trace THEN E( "ObjectType" ) END;
			RETURN pointerType
		END ObjectType;


		(** CellType = 'cell' [ParameterList] DeclarationSequence [Body] 'end' [Identifier]
              | 'object'. **)
		PROCEDURE CellType(position: LONGINT;  name: SyntaxTree.Identifier; parentScope: SyntaxTree.Scope; isCellNet: BOOLEAN): SyntaxTree.Type;
		VAR
			cellType: SyntaxTree.CellType;
			cellScope: SyntaxTree.CellScope;
			modifiers: SyntaxTree.Modifier;
		BEGIN
			IF Trace THEN S( "CellType" ) END;
			(* symbol cell already consumed *)

			cellScope := SyntaxTree.NewCellScope(parentScope);
			cellType := SyntaxTree.NewCellType( position, parentScope,cellScope);
			cellType.IsCellNet(isCellNet);
			cellScope.SetOwnerCell(cellType);


			IF Optional(Scanner.LeftBrace) THEN
				modifiers := Flags();
				cellType.SetModifiers(modifiers);
			END;


			IF Optional( Scanner.LeftParenthesis ) THEN
				PortList(cellType,cellScope);
			END;

			DeclarationSequence( cellScope);
			IF Peek(Scanner.Begin) OR Peek(Scanner.Code) THEN
				cellScope.SetBodyProcedure(BodyProcedure(cellScope));
			END;
			Check(Scanner.End);

			IF ExpectThisIdentifier( name ) THEN
				(* check name not always, reflect in EBNF? *)
			END;
			IF Trace THEN E( "CellType" ) END;
			RETURN cellType
		END CellType;

		(** PointerType = 'pointer' 'to' Type. **)
		PROCEDURE PointerType( position: LONGINT; parentScope: SyntaxTree.Scope ): SyntaxTree.PointerType;
		VAR pointerType: SyntaxTree.PointerType;  base: SyntaxTree.Type; 	modifiers: SyntaxTree.Modifier;
		BEGIN
			IF Trace THEN S( "PointerType" ) END;
			(* pointer symbol already consumed *)
			pointerType := SyntaxTree.NewPointerType( position ,parentScope);
			IF Optional(Scanner.LeftBrace) THEN
				modifiers := Flags();
				pointerType.SetModifiers(modifiers)
			END;
			Check( Scanner.To );
			base := Type(NIL, parentScope);
			pointerType.SetPointerBase( base );
			IF base IS SyntaxTree.RecordType THEN
				base(SyntaxTree.RecordType).SetPointerType(pointerType);
			END;
			IF Trace THEN E( "PointerType" ) END;
			RETURN pointerType
		END PointerType;

		(**
			RecordType = 'record' ['(' QualifiedIdentifier ')'] [VariableDeclaration {';' VariableDeclaration}] 'end'.
		**)
		PROCEDURE RecordType(position: LONGINT;  parentScope:SyntaxTree.Scope ): SyntaxTree.RecordType;
		VAR
			recordType: SyntaxTree.RecordType;
			recordScope: SyntaxTree.RecordScope;
			qualifiedIdentifier: SyntaxTree.QualifiedIdentifier;  flags: SET;  qualifiedType: SyntaxTree.QualifiedType;
		BEGIN
			IF Trace THEN S( "RecordType" ) END;
			(* record symbol already consumed *)

			flags := {};
			recordScope := SyntaxTree.NewRecordScope(parentScope);
			recordType := SyntaxTree.NewRecordType( position, parentScope, recordScope);
			IF Optional( Scanner.LeftParenthesis ) THEN
				qualifiedIdentifier := QualifiedIdentifier();
				qualifiedType := SyntaxTree.NewQualifiedType(qualifiedIdentifier.suffix.position, parentScope, qualifiedIdentifier );
				recordType.SetBaseType( qualifiedType );
				Check( Scanner.RightParenthesis )
			END;
			IF Lax THEN
				WHILE Peek(Scanner.Identifier) DO VariableDeclaration(recordScope); Ignore(Scanner.Semicolon) END;
			ELSE
				REPEAT
					IF Peek(Scanner.Identifier) THEN VariableDeclaration( recordScope ) END;
				UNTIL ~Optional( Scanner.Semicolon );
			END;
			Check( Scanner.End );
			IF Trace THEN E( "RecordType" ) END;
			RETURN recordType
		END RecordType;

		(** ArrayType     = 'array' 'of' Type | 'array' Expression {',' Expression}] 'of' Type | '[' MathArraySize {',' MathArraySize} ']' ['of' Type].
	  		 MathArraySize = Expression | '*' | '?'.
		**)
		PROCEDURE ArrayType(position: LONGINT;   parentScope: SyntaxTree.Scope ): SyntaxTree.Type;
		VAR
			arrayType: SyntaxTree.ArrayType;
			type: SyntaxTree.Type;
			base: SyntaxTree.Type;
			expression: SyntaxTree.Expression;

			PROCEDURE MathArray(): SyntaxTree.Type;
			VAR mathType: SyntaxTree.MathArrayType; base: SyntaxTree.Type;
			BEGIN
				IF Optional(Scanner.Questionmark) THEN
					mathType := SyntaxTree.NewMathArrayType(position,parentScope, SyntaxTree.Tensor);
				ELSIF Optional(Scanner.Times) THEN (* open array *)
					mathType := SyntaxTree.NewMathArrayType(position,parentScope, SyntaxTree.Open);
				ELSE (* size given *)
					mathType := SyntaxTree.NewMathArrayType(position,parentScope, SyntaxTree.Static);
					expression := Expression();
					mathType.SetLength(expression);
				END;
				IF Optional(Scanner.Comma) THEN
					base := MathArray()
				ELSIF Mandatory(Scanner.RightBracket) THEN
					IF Optional( Scanner.Of ) THEN
						base := Type(NIL , parentScope );   (* base type *)
					END;
				END;
				mathType.SetArrayBase(base);
				RETURN mathType;
			END MathArray;

		BEGIN
			IF Trace THEN S( "ArrayType" ) END;
			(* array symbol already consumed *)
			IF Optional(Scanner.LeftBracket) THEN (* math array *)
				type := MathArray();
			ELSIF Optional( Scanner.Of ) THEN  (* open array *)
				arrayType := SyntaxTree.NewArrayType(position,parentScope, SyntaxTree.Open);
				type := arrayType;
				base := Type( NIL ,parentScope);
				arrayType.SetArrayBase( base )
			ELSE (* static array *)
				arrayType := SyntaxTree.NewArrayType(position,parentScope, SyntaxTree.Static);
				type := arrayType;
				expression := SimpleExpression();
				arrayType.SetLength( expression );
				position := symbol.start;
				IF Optional( Scanner.Comma ) THEN
					base := ArrayType( position,parentScope);
					arrayType.SetArrayBase( base )
				ELSIF Mandatory( Scanner.Of ) THEN
					base := Type(NIL , parentScope );   (* base type *)
					arrayType.SetArrayBase( base );
				END;
			END;
			IF Trace THEN E( "ArrayType" ) END;
			RETURN type
		END ArrayType;

		(** EnumerationType = 'enum' Identifier {',' Identifier} 'end'. *)
		PROCEDURE EnumerationType(position: LONGINT; parentScope: SyntaxTree.Scope): SyntaxTree.Type;
		VAR type: SyntaxTree.EnumerationType; scope: SyntaxTree.EnumerationScope; identifier: SyntaxTree.Identifier;
			qualifiedIdentifier: SyntaxTree.QualifiedIdentifier; qualifiedType: SyntaxTree.QualifiedType; access: SET;
			constant: SyntaxTree.Constant; expression: SyntaxTree.Expression;
		BEGIN
			scope := SyntaxTree.NewEnumerationScope(parentScope);
			type := SyntaxTree.NewEnumerationType(position,parentScope, scope);
			IF Optional( Scanner.LeftParenthesis ) THEN
				qualifiedIdentifier := QualifiedIdentifier();
				qualifiedType := SyntaxTree.NewQualifiedType(qualifiedIdentifier.suffix.position, parentScope, qualifiedIdentifier );
				type.SetEnumerationBase( qualifiedType );
				Check( Scanner.RightParenthesis )
			END;
			REPEAT
				IdentifierDefinition(identifier,access,FALSE);
				position := symbol.start;
				constant := SyntaxTree.NewConstant( position, identifier );
				CommentSymbol(constant);
				constant.SetAccess(access * SyntaxTree.ReadOnly);
				IF Optional(Scanner.Equal) THEN
					expression := Expression();
					constant.SetValue( expression );
				END;
				scope.AddConstant( constant );
			UNTIL ~Optional(Scanner.Comma);
			IF Mandatory(Scanner.End) THEN END;
			RETURN type
		END EnumerationType;

		(** PortType = (sender|receiver) 'of' Type. *)
		PROCEDURE PortType(position: LONGINT; parentScope: SyntaxTree.Scope): SyntaxTree.Type;
		VAR type: SyntaxTree.Type; direction: LONGINT; sizeExpression: SyntaxTree.Expression;
		BEGIN
			IF Optional(Scanner.In) THEN
				direction := SyntaxTree.InPort
			ELSIF Optional(Scanner.Out) THEN
				direction := SyntaxTree.OutPort
			ELSE
				Error(position,Diagnostics.Invalid,"invalid direction, expected IN or OUT");
			END;

			IF Optional(Scanner.LeftParenthesis) THEN
				sizeExpression := Expression();
				IF Mandatory(Scanner.RightParenthesis )THEN END;
			END;
			type := SyntaxTree.NewPortType(position, direction, sizeExpression, parentScope);
			RETURN type
		END PortType;

		(** Type = ArrayType | RecordType | PointerType | ObjectType | ProcedureType
					  | EnumerationType | QualifiedIdentifier. *)
		PROCEDURE Type( name: SyntaxTree.Identifier; parentScope: SyntaxTree.Scope ): SyntaxTree.Type;
		VAR type: SyntaxTree.Type;  qualifiedIdentifier: SyntaxTree.QualifiedIdentifier;  position: LONGINT;
		BEGIN
			IF Trace THEN S( "Type" ) END;
			position := symbol.start;
			IF Optional( Scanner.Array ) THEN type := ArrayType( position,parentScope );
			ELSIF Optional( Scanner.Record ) THEN type := RecordType( position,parentScope );
			ELSIF Optional( Scanner.Pointer ) THEN type := PointerType( position,parentScope );
			ELSIF Optional( Scanner.Object ) THEN type := ObjectType( position,name,parentScope );
			ELSIF Optional( Scanner.Cell) THEN type := CellType( position, name, parentScope,FALSE);
			ELSIF Optional( Scanner.CellNet) THEN type := CellType( position, name, parentScope, TRUE);
			ELSIF Optional( Scanner.Port) THEN type := PortType( position, parentScope)
			ELSIF Optional( Scanner.Procedure ) THEN type := ProcedureType( position,parentScope);
			ELSIF Optional( Scanner.Enum ) THEN type := EnumerationType( position,parentScope);
			ELSE qualifiedIdentifier := QualifiedIdentifier();
				type := SyntaxTree.NewQualifiedType( qualifiedIdentifier.suffix.position, parentScope, qualifiedIdentifier );
			END;
			IF Trace THEN E( "Type" ) END;
			RETURN type
		END Type;

		(** PortDeclaration = ('out' | 'in') Identifier {',' Identifier}':' Type. **)
		PROCEDURE PortDeclaration(cell: SyntaxTree.CellType; parentScope: SyntaxTree.Scope);
		VAR
			type: SyntaxTree.Type; name: SyntaxTree.Identifier;
			firstParameter, parameter: SyntaxTree.Parameter;
		BEGIN
			IF Trace THEN S( "PortDeclaration" ) END;
			firstParameter := cell.lastParameter;
			REPEAT
				name := Identifier();
				parameter := SyntaxTree.NewParameter(name.position,cell,name,SyntaxTree.ValueParameter);
				cell.AddParameter(parameter);
			UNTIL ~Optional( Scanner.Comma );
			Check( Scanner.Colon );
			type := Type( NIL, parentScope);
			ASSERT(type # NIL);
			IF firstParameter # NIL THEN parameter := firstParameter.nextParameter ELSE parameter := cell.firstParameter END;
			WHILE parameter # NIL DO
				parameter.SetType( type );
				parameter := parameter.nextParameter;
			END;
			IF Trace THEN E( "PortDeclaration" )
			END;
		END PortDeclaration;

		(** PortList = '('[ParameterDeclaration {';' ParameterDeclaration}]')' [':' Type]. **)
		PROCEDURE PortList( cell: SyntaxTree.CellType ; parentScope: SyntaxTree.Scope);
		BEGIN
			IF Trace THEN S( "PortList" ) END;
			(* left parenthesis already consumed *)
			IF ~Optional( Scanner.RightParenthesis ) THEN
				IF Lax THEN
					WHILE Peek(Scanner.Identifier) OR Peek(Scanner.Var) OR Peek(Scanner.Const) DO PortDeclaration( cell, parentScope ); Ignore(Scanner.Semicolon) END;
				ELSE
					REPEAT PortDeclaration( cell, parentScope );  UNTIL ~Optional( Scanner.Semicolon );
				END;
				Check( Scanner.RightParenthesis );
			END;
			IF Trace THEN E( "PortList" ) END;
		END PortList;

		(** ParameterDeclaration = ['var'|'const'] Identifier {',' Identifier}':' Type.**)
		PROCEDURE ParameterDeclaration( procedureType: SyntaxTree.ProcedureType ; parentScope: SyntaxTree.Scope);
		VAR
			type: SyntaxTree.Type; name: SyntaxTree.Identifier;
			firstParameter, parameter: SyntaxTree.Parameter;   kind: LONGINT;
		BEGIN
			IF Trace THEN S( "ParameterDeclaration" ) END;
			IF Optional( Scanner.Var ) THEN (* var parameter *)
				kind := SyntaxTree.VarParameter
			ELSIF Optional( Scanner.Const ) THEN (* const parameter *)
				kind := SyntaxTree.ConstParameter
			ELSIF symbol.token # Scanner.Identifier THEN
				Error(symbol.start,Scanner.Identifier,"");
				RETURN
			ELSE kind := SyntaxTree.ValueParameter
			END;
			firstParameter := procedureType.lastParameter;
			REPEAT
				name := Identifier();
				parameter := SyntaxTree.NewParameter(name.position,procedureType,name,kind);
				procedureType.AddParameter(parameter);
				IF Optional(Scanner.Equal) THEN
					parameter.SetDefaultValue(Expression());
				END
			UNTIL ~Optional( Scanner.Comma );
			Check( Scanner.Colon );
			type := Type( NIL, parentScope);
			ASSERT(type # NIL);
			IF firstParameter # NIL THEN parameter := firstParameter.nextParameter ELSE parameter := procedureType.firstParameter END;
			WHILE parameter # NIL DO
				parameter.SetType( type );
				parameter := parameter.nextParameter;
			END;
			IF Trace THEN E( "ParameterDeclaration" )
			END;
		END ParameterDeclaration;

		(** FormalParameters = '('[ParameterDeclaration {';' ParameterDeclaration}]')' [':' Type]. **)
		PROCEDURE FormalParameters( procedureType: SyntaxTree.ProcedureType ; parentScope: SyntaxTree.Scope);
		VAR type: SyntaxTree.Type; position: LONGINT;
		BEGIN
			IF Trace THEN S( "FormalParameters" ) END;
			(* left parenthesis already consumed *)
			IF ~Optional( Scanner.RightParenthesis ) THEN
				IF Lax THEN
					WHILE Peek(Scanner.Identifier) OR Peek(Scanner.Const) OR Peek(Scanner.Var) DO
						ParameterDeclaration(procedureType, parentScope); Ignore(Scanner.Semicolon)
					END;
				ELSE
					REPEAT ParameterDeclaration( procedureType, parentScope );  UNTIL ~Optional( Scanner.Semicolon );
				END;
				Check( Scanner.RightParenthesis );
			END;
			IF Optional( Scanner.Colon ) THEN
				position:= symbol.start;
				type := Type(NIL,parentScope);
				(* formally, any type is permitted as return type. Actually some of them might simply not be usable *)
				procedureType.SetReturnType(type);
			END;
			IF Trace THEN E( "FormalParameters" ) END;
		END FormalParameters;


		(** Flags = '{' [Identifier ['(' Expression ')'] {',' Identifier ['(' Expression ')'] }]  '}'. **)
		PROCEDURE Flags(): SyntaxTree.Modifier;
		VAR identifier: SyntaxTree.Identifier; modifier,list: SyntaxTree.Modifier; position: LONGINT; expression: SyntaxTree.Expression;
		BEGIN
			IF Trace THEN S( "Flags" ) END;
			(* left brace already consumed *)
			list := NIL;
			IF Peek(Scanner.RightBrace) THEN (* empty flags *)
			ELSE
				REPEAT
					position := symbol.start;
					identifier := Identifier();
					IF Optional(Scanner.LeftParenthesis) THEN
						expression := Expression();
						Check(Scanner.RightParenthesis)
					ELSIF Optional(Scanner.Equal) THEN
						expression := Expression();
					ELSE
						expression := NIL
					END;
					modifier := SyntaxTree.NewModifier(identifier,expression);
					AppendModifier(list,modifier);
				UNTIL ~Optional( Scanner.Comma ) & ~Optional(Scanner.Semicolon);
			END;
			Check(Scanner.RightBrace);
			IF Trace THEN E( "Flags" ) END;
			RETURN list;
		END Flags;

		PROCEDURE CommentSymbol(symbol: SyntaxTree.Symbol);
		BEGIN
			IF (recentComment # NIL) & (recentComment.nextSymbol = NIL) THEN
				recentComment.SetNextSymbol(symbol);
			END;
			recentSymbol := symbol
		END CommentSymbol;


		(** ProcedureDeclaration = 'procedure' ['&'|'-'|Flags ['-']] IdentifierDefinition [FormalParameters]';'
			                       DeclarationSequence  [Body] 'end' Identifier.
		**)
		PROCEDURE ProcedureDeclaration( parentScope: SyntaxTree.Scope);
		VAR name: SyntaxTree.Identifier;
			procedure: SyntaxTree.Procedure;
			procedureType: SyntaxTree.ProcedureType;
			procedureScope : SyntaxTree.ProcedureScope;
			access: SET;
			position: LONGINT;
			isConstructor: BOOLEAN;
			isInline: BOOLEAN;
			modifiers: SyntaxTree.Modifier;
		BEGIN
			IF Trace THEN S( "Procedure" ) END;
			(* symbol procedure has already been consumed *)

			modifiers := NIL;
			isConstructor := FALSE; isInline := FALSE;

			procedureType := SyntaxTree.NewProcedureType(symbol.start, parentScope);
			isConstructor := FALSE; isInline := FALSE;
			IF Optional( Scanner.And ) THEN  (* constructor *)
				isConstructor := TRUE
			ELSIF Optional( Scanner.Minus ) THEN  (* inline *)
				isInline := TRUE;
			ELSIF Optional( Scanner.LeftBrace) THEN
				modifiers := Flags();
				IF Optional( Scanner.Minus ) THEN  (* inline *)
					isInline := TRUE
				END;
			END;

			IF Peek(Scanner.String) OR Peek(Scanner.Character)  THEN (* for compatibility with release *)
				OperatorDeclaration( parentScope );  RETURN
			END;

			position:= symbol.start;
			IdentifierDefinition( name, access,FALSE);

			procedureScope := SyntaxTree.NewProcedureScope(parentScope);
			procedure := SyntaxTree.NewProcedure( position, name, procedureScope);
			procedure.SetConstructor(isConstructor);
			procedure.SetInline(isInline);
			CommentSymbol(procedure);
			procedure.SetAccess(access * SyntaxTree.ReadOnly);

			procedureType.SetModifiers(modifiers);
			procedure.SetType(procedureType);
			IF Optional(Scanner.LeftParenthesis) THEN FormalParameters( procedureType, procedureScope) END;
			IF Lax THEN Ignore(Scanner.Semicolon) ELSE Check( Scanner.Semicolon ) END;
			DeclarationSequence( procedureScope);
			IF Peek(Scanner.Begin) OR Peek(Scanner.Code) THEN
				procedureScope.SetBody(Body(procedureScope));
			END;
			Check(Scanner.End);
			IF ExpectThisIdentifier( name ) THEN END;
			parentScope.AddProcedure( procedure );

			IF Trace THEN E( "Procedure") END;
		END ProcedureDeclaration;

		(** OperatorDeclaration  = 'operator' String ['*'|'-'] FormalParameters ';'
			                       DeclarationSequence [Body] 'end' String.
		**)
		PROCEDURE OperatorDeclaration(parentScope: SyntaxTree.Scope );
		VAR
			string: Scanner.StringType; name: Scanner.StringType;
			procedureScope: SyntaxTree.ProcedureScope;
			procedureType: SyntaxTree.ProcedureType;
			operator: SyntaxTree.Operator;
			access: SET;
			i: LONGINT; ch: CHAR; position: LONGINT;
		BEGIN
			IF Trace THEN S( "Operator" ) END;
			(* symbol operator already consumed *)
			position := symbol.start;
			IF MandatoryString( string ) THEN
				(* copy string to name and check for length. LEN(name)>0, LEN(string)>0 can be presumed  *)
				i := 0;
				REPEAT
					ch := string[i];
					name[i] := ch;
					INC(i);
				UNTIL (ch = 0X) OR (i=LEN(string)) OR (i=LEN(name));
				IF ch # 0X THEN (* string too long to act as operator identifier *)
					Error(symbol.start,Basic.StringTooLong,"");
					name := "";
				END;
			ELSE
				name := "";
			END;
			IF Optional( Scanner.Times ) THEN access := SyntaxTree.ReadOnly;
			ELSIF Optional( Scanner.Minus ) THEN access := SyntaxTree.ReadOnly;
			ELSE access := SyntaxTree.Internal;
			END;
			procedureScope := SyntaxTree.NewProcedureScope(parentScope);
			operator := SyntaxTree.NewOperator( symbol.start, SyntaxTree.NewIdentifier(position,name), procedureScope);
			CommentSymbol(operator);
			operator.SetAccess(access * SyntaxTree.ReadOnly);
			procedureType := SyntaxTree.NewProcedureType(symbol.start,parentScope);
			IF Mandatory(Scanner.LeftParenthesis) THEN FormalParameters( procedureType, procedureScope ) END;
			operator.SetType( procedureType );
			IF Lax THEN Ignore(Scanner.Semicolon) ELSE Check( Scanner.Semicolon ) END;
			DeclarationSequence( procedureScope );
			IF Peek(Scanner.Begin) OR Peek(Scanner.Code) THEN
				procedureScope.SetBody(Body(procedureScope));
			END;
			IF Mandatory(Scanner.End) & ExpectThisString(string) THEN END;
			parentScope.AddProcedure(operator);
			IF parentScope IS SyntaxTree.ModuleScope THEN
				parentScope(SyntaxTree.ModuleScope).AddOperator(operator);
			ELSIF parentScope IS SyntaxTree.RecordScope THEN
				parentScope(SyntaxTree.RecordScope).AddOperator(operator);
			ELSE
				Error(position,Diagnostics.Invalid,"Operators only allowed in module scope");
			END;
			IF Trace THEN EE( "Operator", name ) END;
		END OperatorDeclaration;

		(** VariableNameList = IdentifierDefinition [Flags] {',' IdentifierDefinition [Flags]}.**)
		PROCEDURE VariableNameList( scope: SyntaxTree.Scope );
		VAR varname: SyntaxTree.Identifier;  position: LONGINT; variable: SyntaxTree.Variable;  flags,access: SET;
		BEGIN
			IF Trace THEN S( "VariableNameList" ) END;
			REPEAT
				flags := {};
				position := symbol.start;
				IdentifierDefinition( varname, access,TRUE);
				variable := SyntaxTree.NewVariable( position, varname );
				CommentSymbol(variable);
				IF Optional(Scanner.LeftBrace) THEN variable.SetModifiers(Flags()) END;
				variable.SetAccess(access);
				scope.AddVariable(variable);
			UNTIL ~Optional( Scanner.Comma );
			IF Trace THEN E( "VariableNameList" ) END;
		END VariableNameList;

		(** VariableDeclaration = VariableNameList ':' Type. **)
		PROCEDURE VariableDeclaration(parentScope: SyntaxTree.Scope );
		VAR
			variable, firstVariable: SyntaxTree.Variable; type: SyntaxTree.Type;
		BEGIN
			IF Trace THEN S( "VariableDeclaration" ) END;
			firstVariable := parentScope.lastVariable;
			VariableNameList( parentScope );
			Check( Scanner.Colon );
			type := Type( NIL, parentScope );

			variable := firstVariable;
			IF firstVariable #  NIL THEN variable := firstVariable.nextVariable ELSE variable := parentScope.firstVariable END;
			WHILE variable # NIL  DO
				variable.SetType( type );
				variable := variable.nextVariable;
			END;
			IF Trace THEN E( "VariableDeclaration" ) END;
		END VariableDeclaration;

		(** TypeDeclaration = IdentifierDefinition '=' Type.**)
		PROCEDURE TypeDeclaration(parentScope: SyntaxTree.Scope);
		VAR name: SyntaxTree.Identifier;  position: LONGINT; type: SyntaxTree.Type; typeDeclaration: SyntaxTree.TypeDeclaration;   access: SET;
		BEGIN
			IF Trace THEN S( "TypeDeclaration" ) END;
			position := symbol.start;
			IdentifierDefinition( name, access,FALSE);
			typeDeclaration := SyntaxTree.NewTypeDeclaration( position,name);
			CommentSymbol(typeDeclaration);
			Check( Scanner.Equal );
			type := Type( name , parentScope);
			type.SetTypeDeclaration(typeDeclaration);
			typeDeclaration.SetDeclaredType(type);
			(*
			type.SetName(typeDeclaration.name);  (* don't do that: overwrites global names ! *)
			*)
			typeDeclaration.SetAccess(access * SyntaxTree.ReadOnly);
			parentScope.AddTypeDeclaration( typeDeclaration );
			IF Trace THEN E( "TypeDeclaration" ) END;
		END TypeDeclaration;

		(** ConstDeclaration = IdentifierDefinition '=' Expression. **)
		PROCEDURE ConstDeclaration(parentScope: SyntaxTree.Scope );
		VAR name: SyntaxTree.Identifier;  position: LONGINT; constant: SyntaxTree.Constant;  expression: SyntaxTree.Expression;  access: SET;
		BEGIN
			IF Trace THEN S( "ConstDeclaration" ) END;
			IdentifierDefinition( name, access, FALSE);
			position := symbol.start;
			constant := SyntaxTree.NewConstant( position, name );
			CommentSymbol(constant);
			constant.SetAccess(access * SyntaxTree.ReadOnly);
			Check( Scanner.Equal );
			expression := Expression();
			constant.SetValue( expression );
			parentScope.AddConstant( constant );
			IF Trace THEN E( "ConstDeclaration" ) END;
		END ConstDeclaration;

		(** DeclarationSequence  =  { 'const' [ConstDeclaration] {';' [ConstDeclaration]}
			                         |'type'  [TypeDeclaration] {';' [TypeDeclaration]}
			                         |'var'   [VariableDeclaration] {';' [VariableDeclaration]}
			                        }
			                        [ProcedureDeclaration | OperatorDeclaration]
			                        {';' [ProcedureDeclaration | OperatorDeclaration] }.
		**)
		PROCEDURE DeclarationSequence( parentScope: SyntaxTree.Scope);
		VAR previousScope: SyntaxTree.Scope;
		BEGIN
			previousScope := currentScope;
			currentScope := parentScope;
			IF Trace THEN S( "DeclarationSequence" ) END;
			IF Lax THEN
				LOOP
					Ignore(Scanner.Semicolon);
					IF Optional(Scanner.Const) THEN
						WHILE Peek(Scanner.Identifier) DO ConstDeclaration(parentScope); Ignore(Scanner.Semicolon) END;
					ELSIF Optional(Scanner.Type) THEN
						WHILE Peek(Scanner.Identifier) DO TypeDeclaration(parentScope); Ignore(Scanner.Semicolon) END;
					ELSIF Optional(Scanner.Var) THEN
						WHILE Peek(Scanner.Identifier) DO VariableDeclaration(parentScope); Ignore(Scanner.Semicolon); END;
					ELSIF Optional(Scanner.Procedure) THEN
						ProcedureDeclaration(parentScope); Ignore(Scanner.Semicolon)
					ELSIF Optional(Scanner.Operator) THEN
						OperatorDeclaration(parentScope); Ignore(Scanner.Semicolon);
					ELSE
						EXIT
					END;
				END;
			ELSE
				LOOP
					IF Optional( Scanner.Const ) THEN
						REPEAT
							IF Peek(Scanner.Identifier) THEN ConstDeclaration( parentScope ) END
						UNTIL ~Optional( Scanner.Semicolon )
					ELSIF Optional( Scanner.Type ) THEN
						REPEAT
							IF Peek(Scanner.Identifier) THEN TypeDeclaration( parentScope) END
						UNTIL ~Optional( Scanner.Semicolon )
					ELSIF Optional( Scanner.Var ) THEN
						REPEAT
							IF Peek(Scanner.Identifier) THEN VariableDeclaration( parentScope ) END
						UNTIL ~Optional( Scanner.Semicolon )
					ELSE EXIT
					END;
					Ignore(Scanner.Semicolon)
				END;
				REPEAT
					IF Optional( Scanner.Operator ) THEN
						OperatorDeclaration( parentScope);
					ELSIF Optional( Scanner.Procedure ) THEN
						ProcedureDeclaration( parentScope );
					END;
				UNTIL ~Optional( Scanner.Semicolon );
			END;
			currentScope := previousScope;
			IF Trace THEN E( "DeclarationSequence" ) END;
		END DeclarationSequence;

		(**
			ImportList = 'import' Import { ',' Import } ';'.
			Import     = Identifier [':=' Identifier] ['in' Identifier].
		**)
		PROCEDURE ImportList( moduleScope: SyntaxTree.ModuleScope );
		VAR alias, name, context: SyntaxTree.Identifier;  import: SyntaxTree.Import; position: LONGINT;
		BEGIN
			IF Trace THEN S( "ImportList" ) END;
			(* import symbol already consumed *)
			REPEAT
				position := symbol.start;
				alias := Identifier();
				IF alias # SyntaxTree.invalidIdentifier THEN
					IF Optional( Scanner.Becomes ) THEN name := Identifier() ELSE name := alias;  END;
					import := SyntaxTree.NewImport( position, alias, name, TRUE );
					CommentSymbol(import);
					IF Optional(Scanner.In) THEN
						position := symbol.start;
						context := Identifier();
						IF context # SyntaxTree.invalidIdentifier THEN  import.SetContext(context) END;
					END;
					moduleScope.AddImport( import );
				END;
			UNTIL ~Optional( Scanner.Comma );
			IF Lax THEN Ignore(Scanner.Semicolon) ELSE Check( Scanner.Semicolon ) END;
			IF Trace THEN E( "ImportList" );  END;
		END ImportList;

		(** Module = 'module' Identifier ['in' Identifier]';' [ImportList] DeclarationSequence [Body]
			         'end' Identifier '.'. **)
		PROCEDURE Module*(): SyntaxTree.Module;
		VAR moduleName, context: SyntaxTree.Identifier;  module: SyntaxTree.Module;  position: LONGINT; isCellNet: BOOLEAN;
		BEGIN
			IF Trace THEN S( "Module" ) END;
			position := symbol.start;
			moduleScope := SyntaxTree.NewModuleScope(); (* needed to feed in comment already before module starts *)
			currentScope := moduleScope;
			isCellNet := Optional(Scanner.CellNet);
			IF isCellNet OR Mandatory( Scanner.Module ) THEN
				moduleName :=  Identifier();
				module := SyntaxTree.NewModule( scanner.source, moduleName.position, moduleName, moduleScope, scanner.case );
				IF isCellNet THEN module.SetCellNet(TRUE) END;

				module.SetType(SyntaxTree.moduleType);
				CommentSymbol(module);
				IF Optional(Scanner.In) THEN
					position := symbol.start;
					context := Identifier();
					module.SetContext(context);
				END;
				IF Lax THEN Ignore(Scanner.Semicolon) ELSE	Check(Scanner.Semicolon) END;
				IF Optional(Scanner.Import) THEN ImportList(moduleScope) END;
				DeclarationSequence( moduleScope);
				IF Peek(Scanner.Begin) OR Peek(Scanner.Code) THEN
					moduleScope.SetBodyProcedure(BodyProcedure(moduleScope)); (* insert empty body procedure if necessary *)
				END;
				Check(Scanner.End);
				IF ExpectThisIdentifier( moduleName ) THEN
					IF symbol.token # Scanner.Period THEN
						Error(  symbol.start, Scanner.Period, "" )
					END;   (* do not use Check for not reading after end of module *)
				END;
			END;
			IF Trace THEN E( "Module" ) END;
			RETURN module
		END Module;

		(** check if another module declaration is available after recent module parsing -> for parsing and compiling multiple modules within a single file **)
		PROCEDURE NextModule*(): BOOLEAN;
		BEGIN
			scanner.ResetCase;
			NextSymbol; RETURN Peek(Scanner.Module) OR Peek(Scanner.CellNet);
		END NextModule;

	END Parser;

	(* utilities *)
	PROCEDURE AppendModifier(VAR list: SyntaxTree.Modifier; modifier: SyntaxTree.Modifier);
	VAR this, next: SyntaxTree.Modifier;
	BEGIN
		IF list = NIL THEN list := modifier
		ELSE
			this := list;
			next := list.nextModifier;
			WHILE next # NIL DO
				this := next;
				next := this.nextModifier;
			END;
			this.SetNext(modifier);
		END;
	END AppendModifier;

	(** parser retrieval **)
	PROCEDURE NewParser*( scanner: Scanner.Scanner;  diagnostics: Diagnostics.Diagnostics): Parser;
	VAR parser: Parser;
	BEGIN
		NEW( parser, scanner, diagnostics );  RETURN parser;
	END NewParser;

END FoxParser.
