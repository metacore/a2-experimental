MODULE OCPrintout; (** AUTHOR "fof & fn"; PURPOSE "Oberon Compiler Module Output for SymbolFile, Pretty Printing and Testing"; *)
(* (c) fof ETHZ 2009 *)

IMPORT
	Scanner := OCScanner, SyntaxTree := OCSyntaxTree, Global := OCGlobal, Basic := OCBasic,
	Streams,  D:=Debugging, WMGraphics, Runtime, SYSTEM;

CONST
	(* print modes *)
	Exported*=0; SymbolFile*=1; SourceCode*=2;  All*=3;

TYPE

	Printer*= OBJECT (SyntaxTree.Visitor)
	VAR
		w-: Basic.Writer; mode: LONGINT; singleStatement: BOOLEAN;
		currentScope: SyntaxTree.Scope; ws: Streams.StringWriter;
		info: BOOLEAN; case: LONGINT;

		alertCount, commentCount: LONGINT;

		PROCEDURE Small(CONST name: ARRAY OF CHAR; VAR result: ARRAY OF CHAR);
		VAR ch: CHAR; i: LONGINT;
		BEGIN
			i := 0;
			REPEAT
				ch := name[i];
				IF (ch >= 'A') & (ch <= 'Z') THEN
					ch := CHR(ORD(ch)-ORD('A')+ORD('a'));
				END;
				result[i] := ch; INC(i);
			UNTIL ch = 0X;
		END Small;

		PROCEDURE Keyword(CONST a: ARRAY OF CHAR);
		VAR str: ARRAY 64 OF CHAR;
		BEGIN
			IF case= Scanner.Lowercase THEN Small(a,str) ELSE COPY(a,str) END;
			w.SetFontStyle({WMGraphics.FontBold});
			w.String(a);
			w.SetFontStyle({});
		END Keyword;

		PROCEDURE BeginComment;
		BEGIN
			w.BeginComment; w.String("(* ");
		END BeginComment;

		PROCEDURE EndComment;
		BEGIN
			w.String(" *)");w.EndComment
		END EndComment;

		PROCEDURE AlertString(CONST s: ARRAY OF CHAR);
		BEGIN
			w.BeginAlert; w.String(s); w.EndAlert;
		END AlertString;

		PROCEDURE Indent;
		BEGIN w.Ln;
		END Indent;

		PROCEDURE Identifier*(x: SyntaxTree.Identifier);
		VAR str: Scanner.StringType;
		BEGIN
			x.GetString(str); w.String(str);
		END Identifier;

		PROCEDURE QualifiedIdentifier*(x: SyntaxTree.QualifiedIdentifier);
		BEGIN
			IF x.prefix # NIL THEN Identifier(x.prefix); w.String("."); END;
			Identifier(x.suffix);
		END QualifiedIdentifier;

		PROCEDURE Type*(x: SyntaxTree.Type);
		BEGIN
			IF x= NIL THEN
				AlertString("nil type");
			ELSE
				x.Accept(SELF);
			END;
		END Type;

		PROCEDURE VisitType(x: SyntaxTree.Type);
		BEGIN
			IF x = SyntaxTree.importType THEN w.String("importType")
			ELSIF x = SyntaxTree.typeDeclarationType THEN w.String("typeDeclarationType");
			ELSE
				AlertString("InvalidType");
			END;
		END VisitType;

		PROCEDURE VisitBasicType(x: SyntaxTree.BasicType);
		BEGIN
			IF x.typeDeclaration # NIL THEN
				Identifier(x.typeDeclaration.name);
			ELSE
				Identifier(x.name)
			END
		END VisitBasicType;

		PROCEDURE VisitCharacterType(x: SyntaxTree.CharacterType);
		BEGIN
			VisitBasicType(x);
		END VisitCharacterType;

		PROCEDURE VisitIntegerType(x: SyntaxTree.IntegerType);
		BEGIN
			VisitBasicType(x);
		END VisitIntegerType;

		PROCEDURE VisitFloatType(x: SyntaxTree.FloatType);
		BEGIN
			VisitBasicType(x);
		END VisitFloatType;

		PROCEDURE VisitQualifiedType(x: SyntaxTree.QualifiedType);
		BEGIN
			IF x.resolved = SyntaxTree.invalidType THEN
				AlertString("(*unresolved*)");
			END;
			IF x.qualifiedIdentifier # NIL THEN
				QualifiedIdentifier(x.qualifiedIdentifier)
			ELSE
				AlertString("NIL (* missing qualified identifier *)");
			END;
		END VisitQualifiedType;

		PROCEDURE VisitStringType(x: SyntaxTree.StringType);
		BEGIN
			w.String("STRING"); w.String("(* len = "); w.Int(x.length,1); w.String(" *)");
		END VisitStringType;

		PROCEDURE VisitEnumerationType(x: SyntaxTree.EnumerationType);
		VAR e: SyntaxTree.Constant; first: BOOLEAN;
		BEGIN
			Keyword("ENUM ");

			IF x.enumerationBase # NIL THEN
				w.String("(");
					Type(x.enumerationBase);
				w.String(") ");
			END;

			e := x.enumerationScope.firstConstant; first := TRUE;
			WHILE (e # NIL) DO
				IF ~first THEN w.String(",") ELSE first := FALSE END;
				VisitConstant(e);
				e := e.nextConstant;
			END;


			Keyword(" END");
		END VisitEnumerationType;

		PROCEDURE VisitRangeType(x: SyntaxTree.RangeType);
		BEGIN
			w.String("RANGE"); w.String("(* commonType = "); Type(x.commonType); w.String("*)");
		END VisitRangeType;

		PROCEDURE VisitArrayType(x: SyntaxTree.ArrayType);
		BEGIN
			Keyword("ARRAY " );
			IF x.length # NIL THEN Expression(x.length);
			w.String( " " );  END;
			Keyword("OF " );
			Type(x.arrayBase);
		END VisitArrayType;

		PROCEDURE VisitMathArrayType(x: SyntaxTree.MathArrayType);
		BEGIN
			Keyword("ARRAY " );
			IF x.form = SyntaxTree.Tensor THEN w.String("[?] ");
			ELSE
				w.String("[");
				IF x.length = NIL THEN
					w.String("*")
				ELSE
					Expression(x.length);
				END;
				WHILE(x.arrayBase # NIL) & (x.arrayBase IS SyntaxTree.MathArrayType) DO
					x := x.arrayBase(SyntaxTree.MathArrayType);
					w.String(", ");
					IF x.length = NIL THEN
						w.String("*")
					ELSE
						Expression(x.length);
					END;
				END;
				w.String("] ");
			END;
			Keyword("OF " );
			Type(x.arrayBase);
		END VisitMathArrayType;

		PROCEDURE VisitPointerType(x: SyntaxTree.PointerType);
		VAR pointerBase: SyntaxTree.Type;
		BEGIN
			IF x.pointerBase = NIL THEN
				w.BeginAlert; Keyword("POINTER TO NIL"); w.EndAlert;
			ELSE
				pointerBase := x.pointerBase;
				IF (pointerBase IS SyntaxTree.RecordType) & (pointerBase(SyntaxTree.RecordType).isObject) THEN
					VisitRecordType(pointerBase(SyntaxTree.RecordType))
				ELSE
					Keyword("POINTER TO " );  Type(x.pointerBase)
				END;
			END;
		END VisitPointerType;

		PROCEDURE VisitRecordType(x: SyntaxTree.RecordType);
		VAR prevScope: SyntaxTree.Scope;
		BEGIN
			IF x.isObject THEN
				Keyword("OBJECT ");
				IF info THEN BeginComment; w.String("ObjectType"); EndComment;  END;
				IF (x.baseType # NIL)  THEN
					w.String( "(" );
					IF (x.baseType IS SyntaxTree.RecordType) & (x.baseType(SyntaxTree.RecordType).pointerType # NIL) THEN
						Type(x.baseType(SyntaxTree.RecordType).pointerType)
					ELSE
						Type(x.baseType);
					END;
					w.String( ")" );
				END;
				Scope(x.recordScope);

				IF (x.recordScope.bodyProcedure # NIL) THEN
					Body(x.recordScope.bodyProcedure.procedureScope.body)
				END;

				Indent; Keyword("END ");
				IF (x.pointerType # NIL) & (x.pointerType.typeDeclaration # NIL) THEN
					Identifier(x.pointerType.typeDeclaration.name);
				END;
			ELSE
				Keyword("RECORD ");
				IF (x.baseType # NIL) THEN
					w.String( "(" );
					IF (x.baseType IS SyntaxTree.RecordType) & (x.baseType(SyntaxTree.RecordType).pointerType # NIL) THEN
						Type(x.baseType(SyntaxTree.RecordType).pointerType)
					ELSE
						Type(x.baseType);
					END;
					w.String( ")" );
				END;
				prevScope := currentScope;
				currentScope := x.recordScope;
				VariableList(x.recordScope.firstVariable);
				currentScope := prevScope;
				Indent; Keyword("END" );
			END;
		END VisitRecordType;

		PROCEDURE Flags(flags: SET);
		VAR first: BOOLEAN;
			PROCEDURE Flag(CONST name: ARRAY OF CHAR);
			BEGIN
				IF first THEN w.String("{"); first := FALSE; ELSE w.String(", ") END;
				w.String(name);
			END Flag;
		BEGIN
			first := TRUE;
			IF SyntaxTree.ActiveFlag IN flags THEN Flag("ACTIVE") END;
			IF SyntaxTree.ExclusiveFlag IN flags THEN Flag("EXCLUSIVE") END;
			IF SyntaxTree.SafeFlag IN flags THEN Flag("SAFE") END;
			IF SyntaxTree.RealtimeFlag IN flags THEN Flag("REALTIME") END;
			IF SyntaxTree.WinAPIFlag IN flags THEN Flag("WINAPI") END;
			IF SyntaxTree.CFlag IN flags THEN Flag("C") END;
			IF SyntaxTree.DelegateFlag IN flags THEN Flag("DELEGATE") END;
			IF SyntaxTree.UntracedFlag IN flags THEN Flag("UNTRACED") END;
			IF ~first THEN w.String("} ") END;

			IF info THEN
				BeginComment;
				IF SyntaxTree.AccessedFlag IN flags THEN Flag("ACCESSED") END;
				IF SyntaxTree.WrittenFlag IN flags THEN Flag("WRITTEN") END;
				IF SyntaxTree.UnreachableFlag IN flags THEN Flag("UNREACHABLE") END;
				IF ~first THEN w.String("}") END;
				EndComment;
			END;
		END Flags;

		PROCEDURE VisitProcedureType(x: SyntaxTree.ProcedureType);
		BEGIN
			Keyword("PROCEDURE " );
			IF (x.flagList = NIL) THEN Flags(x.flags) ELSE Modifiers(x.flagList) END;
			IF info THEN
				BeginComment;
				Flags(x.flags);
				EndComment;
			END;
			(*
			CallingConvention(x.callingConvention);
			IF x.isDelegate THEN w.String("{DELEGATE}") END;
			*)
			IF (x.firstParameter # NIL) OR (x.returnType # NIL) THEN
				ParameterList(x.firstParameter)
			END;
			IF x.returnType # NIL THEN w.String( ":" );  Type(x.returnType) END;
			IF info & (x.returnParameter # NIL) THEN
				BeginComment;
				VisitParameter(x.returnParameter);
				EndComment;
			END;

		END VisitProcedureType;

		(*** expressions ****)

		PROCEDURE ExpressionList(x: SyntaxTree.ExpressionList);
		VAR i: LONGINT;  expression: SyntaxTree.Expression;
		BEGIN
			FOR i := 0 TO x.Length() - 1 DO
				expression := x.GetExpression( i );  Expression(expression);
				IF i < x.Length() - 1 THEN w.String( ", " );  END;
			END;
		END ExpressionList;

		PROCEDURE Expression*(x: SyntaxTree.Expression);
		BEGIN
			IF x = NIL THEN
				AlertString("nil expression");
			ELSE
				x.Accept(SELF);
				IF info & (x.resolved # NIL) & (x.resolved # x) THEN
					BeginComment; w.String("value = "); Expression(x.resolved); EndComment;
				END;
			END;
			w.Update;
		END Expression;

		PROCEDURE VisitExpression(x: SyntaxTree.Expression);
		BEGIN
			AlertString("InvalidExpression");
		END VisitExpression;

		PROCEDURE VisitSet(x: SyntaxTree.Set);
		BEGIN
			w.String( "{" );  ExpressionList(x.elements); w.String( "}" );
		END VisitSet;

		PROCEDURE VisitMathArrayExpression(x: SyntaxTree.MathArrayExpression);
		BEGIN
			w.String( "[" );  ExpressionList(x.elements); w.String( "]" );
		END VisitMathArrayExpression;

		PROCEDURE VisitUnaryExpression(x: SyntaxTree.UnaryExpression);
		VAR identifier: SyntaxTree.Identifier;
		BEGIN
			w.String(" ");
			IF x.operator = Scanner.Transpose THEN
				identifier := Global.GetIdentifier(x.operator,case);
				Expression(x.left);
				Identifier(identifier);
			ELSE
				identifier := Global.GetIdentifier(x.operator,case);
				Identifier(identifier);
				Expression(x.left);
			END;
		END VisitUnaryExpression;

		PROCEDURE VisitBinaryExpression(x: SyntaxTree.BinaryExpression);
		VAR identifier: SyntaxTree.Identifier;
		BEGIN
			w.String( "(" );
			Expression(x.left);
			identifier := Global.GetIdentifier(x.operator,case);
			w.String(" "); Identifier(identifier); w.String(" ");
			Expression(x.right);
			w.String(")");
		END VisitBinaryExpression;

		PROCEDURE VisitRangeExpression(x: SyntaxTree.RangeExpression);
		BEGIN
			IF x.from # NIL THEN Expression(x.from) END;
			w.String(" .. ");
			IF x.to # NIL THEN Expression(x.to) END;
			IF x.by # NIL THEN w.String(" BY "); Expression(x.by) END;
		END VisitRangeExpression;

		PROCEDURE VisitTensorRangeExpression(x: SyntaxTree.TensorRangeExpression);
		BEGIN
			w.String(" ? ");
		END VisitTensorRangeExpression;


		PROCEDURE VisitConversion(x: SyntaxTree.Conversion);
		BEGIN
			IF x.typeExpression # NIL THEN Expression(x.typeExpression); w.String("(");
			ELSIF info THEN BeginComment; ShortType(x.type); w.String("<-"); EndComment;
			END;
			Expression(x.expression);
			IF x.typeExpression # NIL THEN w.String(")") END;
		END VisitConversion;

		PROCEDURE VisitDesignator(x: SyntaxTree.Designator);
		BEGIN
			AlertString("InvalidDesignator");
		END VisitDesignator;

		PROCEDURE VisitIdentifierDesignator(x: SyntaxTree.IdentifierDesignator);
		BEGIN
			IF info THEN AlertString("(*<IdentifierDesignator>*)") END;
			Identifier(x.identifier)
		END VisitIdentifierDesignator;

		PROCEDURE VisitSelectorDesignator(x: SyntaxTree.SelectorDesignator);
		BEGIN
			Expression(x.left);
			w.String(".");
			IF info THEN AlertString("(*<SelectorDesignator>*)") END;
			Identifier(x.identifier);
		END VisitSelectorDesignator;

		PROCEDURE VisitBracketDesignator(x: SyntaxTree.BracketDesignator);
		BEGIN
			Expression(x.left);
		 	IF info THEN AlertString("(*<BracketDesignator>*)") END;
		 	w.String("["); ExpressionList(x.parameters); w.String("]");
		END VisitBracketDesignator;

		PROCEDURE VisitParameterDesignator(x: SyntaxTree.ParameterDesignator);
		BEGIN
			Expression(x.left);
			IF info THEN AlertString("(*<ParameterDesignator>*)") END;
			w.String("("); ExpressionList(x.parameters); w.String(")");
		END VisitParameterDesignator;

		PROCEDURE VisitIndexDesignator(x: SyntaxTree.IndexDesignator);
		BEGIN
			Expression(x.left);
			w.String("["); ExpressionList(x.parameters); w.String("]");
			IF info THEN
				BeginComment;
				w.String("<IndexDesignator:");
				ShortType(x.type);
				w.String(">");
				EndComment
			END;
		END VisitIndexDesignator;

		PROCEDURE VisitArrowDesignator(x: SyntaxTree.ArrowDesignator);
		BEGIN
			Expression(x.left);
			IF info THEN AlertString("(*<ArrowDesignator>*)") END;
			w.String( "^" );
		END VisitArrowDesignator;

		PROCEDURE ShortType(x: SyntaxTree.Type); (* for debug information, to prevent recursion *)
		BEGIN
			IF x = NIL THEN w.String("NIL TYPE")
			ELSIF x IS SyntaxTree.QualifiedType THEN Type(x)
			ELSIF x IS SyntaxTree.BasicType THEN Type(x)
			ELSIF x IS SyntaxTree.ProcedureType THEN w.String("ProcedureType:");ShortType(x(SyntaxTree.ProcedureType).returnType);
			ELSE w.String("(other)") END;
		END ShortType;

		PROCEDURE VisitSymbolDesignator(x: SyntaxTree.SymbolDesignator);
		BEGIN
			IF x.left # NIL THEN
			Expression(x.left); w.String(".");
			END;
			IF x.symbol IS SyntaxTree.Operator THEN
				w.String('"'); Identifier(x.symbol.name); w.String('"');
			ELSE
				Identifier(x.symbol.name)
			END;
			IF info THEN
				BeginComment;
				w.String("<SymbolDesignator:");
				ShortType(x.symbol.type);
				w.String(">");
				EndComment
			END;
		END VisitSymbolDesignator;

		PROCEDURE VisitSupercallDesignator(x: SyntaxTree.SupercallDesignator);
		BEGIN
			Expression(x.left);
			w.String( "^" );
			IF info THEN
				BeginComment;
				w.String("<SupercallDesignator:");
				ShortType(x.type);
				w.String(">");
				EndComment
			END;
		END VisitSupercallDesignator;

		PROCEDURE VisitSelfDesignator(x: SyntaxTree.SelfDesignator);
		BEGIN
			ASSERT(x.left = NIL);
			w.String("SELF");
			IF info THEN
				BeginComment;
				w.String("<SelfDesignator:");
				ShortType(x.type);
				w.String(">");
				EndComment
			END;

		END VisitSelfDesignator;

		PROCEDURE VisitDereferenceDesignator(x: SyntaxTree.DereferenceDesignator);
		BEGIN
			Expression(x.left);
			w.String( "^" );
			IF info THEN
				BeginComment;
				w.String("<DereferenceDesignator:");
				ShortType(x.type);
				w.String(">");
				EndComment
			END;
		END VisitDereferenceDesignator;

		PROCEDURE VisitTypeGuardDesignator(x: SyntaxTree.TypeGuardDesignator);
		BEGIN
			Expression(x.left);
			IF info THEN
				BeginComment;
				w.String("<TypeGuardDesignator:");
				ShortType(x.type);
				w.String(">");
				EndComment
			END;
			w.String("(");
			IF x.typeExpression # NIL THEN Expression(x.typeExpression) ELSE Type(x.type) END;
			w.String(")");
		END VisitTypeGuardDesignator;

		PROCEDURE VisitProcedureCallDesignator(x: SyntaxTree.ProcedureCallDesignator);
		BEGIN
			Expression(x.left);
			IF info THEN
				BeginComment;
				w.String("<ProcedureCallDesignator:");
				ShortType(x.type);
				w.String(">");
				EndComment
			END;
			w.String("("); ExpressionList(x.parameters); w.String(")");
		END VisitProcedureCallDesignator;

		PROCEDURE VisitBuiltinCallDesignator(x: SyntaxTree.BuiltinCallDesignator);
		BEGIN
			IF x.left # NIL THEN
				Expression(x.left);
			ELSE
				w.String("BUILTIN(");
				w.Int(x.id,1);
				w.String(")");
			END;
			IF info THEN
				BeginComment;
				w.String("<BuiltinCallDesignator:");
				ShortType(x.type);
				w.String(">");
				EndComment
			END;
			w.String("("); ExpressionList(x.parameters); w.String(")");
		END VisitBuiltinCallDesignator;

		PROCEDURE VisitValue(x: SyntaxTree.Value);
		BEGIN
			AlertString("InvalidValue");
		END VisitValue;

		PROCEDURE VisitBooleanValue(x: SyntaxTree.BooleanValue);
		BEGIN
			IF Scanner.Uppercase = case THEN
				IF x.value THEN w.String("TRUE" ) ELSE w.String( "FALSE" ) END
			ELSE
				IF x.value THEN w.String("true" ) ELSE w.String( "false" ) END
			END
		END VisitBooleanValue;

		PROCEDURE Hex(x: HUGEINT);
		VAR i,j: LONGINT; a: ARRAY 20 OF CHAR; y: HUGEINT;
		BEGIN
			i := 0;
			REPEAT
				y := x MOD 10H;
				IF y < 10 THEN a[i] := CHR(y+ORD('0'))
				ELSE a[i] := CHR(y-10+ORD('A'))
				END;
				x := x DIV 10H;
				INC(i);
			UNTIL (x=0) OR (i=16);
			IF y >=10 THEN w.Char("0") END;
			REPEAT DEC( i ); w.Char( a[i] ) UNTIL i = 0
		END Hex;

		PROCEDURE VisitIntegerValue(x: SyntaxTree.IntegerValue);

			PROCEDURE InBounds(val: HUGEINT; bits: LONGINT): BOOLEAN;
			VAR m: HUGEINT;
			BEGIN
				m := Runtime.AslH(1,bits-1);
				RETURN (val < m) & (-val <= m)
			END InBounds;
		BEGIN
			(*! use subtype for representation form ?  *)
			IF x.hvalue = MIN(HUGEINT) THEN
				(* special case: display 8000000000000000H without leading minus sign
					to avoid double minus sign for unary expression -8000000000000000H
				*)
				w.Char("0"); w.Hex(x.hvalue,-16); w.Char("H");
			ELSIF InBounds(x.hvalue,32) THEN
				w.Int(SHORT(x.hvalue),1);
			ELSE
				Hex(x.hvalue); w.Char("H");
			END;
		END VisitIntegerValue;

		PROCEDURE VisitCharacterValue(x: SyntaxTree.CharacterValue);
		BEGIN
			Hex( ORD(x.value));  w.String( "X" );
		END VisitCharacterValue;

		PROCEDURE VisitSetValue(x: SyntaxTree.SetValue);
		VAR i: LONGINT;
		BEGIN
			w.String("{");
			i := 0;
			WHILE (i<MAX(SET)) & ~(i IN x.value)  DO
				INC(i);
			END;
			IF i<MAX(SET) THEN
				w.Int(i,1);
				INC(i);
				WHILE i < MAX(SET) DO
					IF i IN x.value THEN w.String(","); w.Int(i,1); END;
					INC(i)
				END
			END;
			w.String("}");
		END VisitSetValue;

		PROCEDURE VisitMathArrayValue(x: SyntaxTree.MathArrayValue);
		BEGIN
			VisitMathArrayExpression(x.array);
		END VisitMathArrayValue;

		PROCEDURE VisitRealValue(x: SyntaxTree.RealValue);
		VAR string: ARRAY 128 OF CHAR; i: LONGINT;
		BEGIN
			IF x.subtype = Scanner.Real THEN
				ws.SetPos(0); ws.Float(x.value,11(*mantissa X.XXXXXXX *)+5(*exponent E+XXX *)); ws.Get(string);
				i := 0;
				WHILE(i<LEN(string)) & (string[i] # 0X) DO
					IF string[i] = "D" THEN string[i] := "E" END;
					INC(i);
				END;
				w.String(string);
			ELSIF x.subtype = Scanner.Longreal THEN
				ws.SetPos(0); ws.Float(x.value,20(*mantissa X.X..(16)..X *)+5(*exponent E+XXX *) ); ws.Get(string);
				i := 0;
				WHILE(i<LEN(string)) & (string[i] # 0X) DO
					IF string[i] = "E" THEN string[i] := "D" END;
					INC(i);
				END;
				w.String(string);
			ELSE
				w.Float(x.value,64)
			END;
		END VisitRealValue;

		PROCEDURE VisitStringValue(x: SyntaxTree.StringValue);
		VAR i: LONGINT;
		BEGIN
			i := 0;
			WHILE (i < LEN( x.value )) & (x.value[i] # 0X) & (x.value[i] # '"') DO INC( i );  END;
			ASSERT(i # LEN(x.value));
			IF  (x.value[i] = 0X) THEN (* no double quotes contained in the string *)
				w.String( '"' );  w.String( x.value );  w.String( '"' );
			ELSE  (* double quotes found in string *)
				w.String( "'" );  w.String( x.value );  w.String( "'" );
			END
		END VisitStringValue;

		PROCEDURE VisitNilValue(x: SyntaxTree.NilValue);
		BEGIN w.String( "NIL" ); IF info THEN BeginComment; Type(x.type); EndComment; END;
		END VisitNilValue;

		PROCEDURE VisitEnumerationValue(x: SyntaxTree.EnumerationValue);
		BEGIN w.Int(x.value,1);
		END VisitEnumerationValue;

		(**** symbols ****)

		PROCEDURE Symbol*(x: SyntaxTree.Symbol);
		BEGIN
			IF x = NIL THEN
				AlertString("nil symbol");
			ELSE
				x.Accept(SELF)
			END
		END Symbol;

		PROCEDURE VisitSymbol(x: SyntaxTree.Symbol);
		BEGIN
			AlertString("InvalidSymbol");
		END VisitSymbol;

		PROCEDURE Visible(symbol: SyntaxTree.Symbol): BOOLEAN;
		BEGIN
			RETURN TRUE (* (SyntaxTree.Public * symbol.access # {}) OR (mode > SymbolFile) *)
				(* using only exported symbols does not work since there might be dependencies ... *)
		END Visible;

		PROCEDURE PrintSymbol(x: SyntaxTree.Symbol);
		BEGIN
			IF x IS SyntaxTree.Operator THEN
				w.String('"');Identifier(x.name);  w.String('"')
			ELSE
				Identifier(x.name)
			END;
			IF SyntaxTree.PublicWrite IN x.access THEN w.String( "*" )
			ELSIF SyntaxTree.PublicRead IN x.access THEN
				IF x IS SyntaxTree.Variable THEN
					w.String( "-" )
				ELSE
					w.String("*")
				END
			ELSIF x.access = {} THEN ASSERT(mode > SourceCode);
				IF info THEN BeginComment; w.String("<- hidden"); EndComment  END;
			END;
			IF info THEN
				BeginComment;
				w.String("access= {");
				Access(x.access);
				w.String("}");
				IF x.offsetInBits # MIN(LONGINT) THEN
					w.String("@"); w.Hex(x.offsetInBits,1);
				END;
				EndComment;
			END;
		END PrintSymbol;

		PROCEDURE VisitTypeDeclaration(x: SyntaxTree.TypeDeclaration);
		BEGIN
			IF Visible(x) THEN
				IF (x.access # SyntaxTree.Hidden) OR (mode > SourceCode) THEN
					PrintSymbol(x);
					w.String(" = ");
					IF x.access # SyntaxTree.Hidden THEN
						Type(x.declaredType);
					ELSE ShortType(x.declaredType)
					END;
				END;
			END;
		END VisitTypeDeclaration;

		PROCEDURE TypeDeclarationList(x: SyntaxTree.TypeDeclaration);
		BEGIN
			Indent;
			Keyword("TYPE " );
			w.IncIndent;
			WHILE(x # NIL) DO
				Indent;
				VisitTypeDeclaration(x);
				w.String( "; " );
				x := x.nextTypeDeclaration;
				IF x # NIL THEN w.Ln END;
			END;
			w.DecIndent;
		END TypeDeclarationList;

		PROCEDURE VisitConstant(x: SyntaxTree.Constant);
		BEGIN
			IF Visible(x) THEN
				IF (mode > SourceCode) OR (x.access # SyntaxTree.Hidden) THEN
					PrintSymbol(x); 
					IF x.value # NIL THEN
						w.String( " = " );  Expression(x.value);
					END;
					IF info THEN BeginComment; ShortType(x.type); EndComment; END;
					IF info & (x.value.resolved = NIL) THEN AlertString("(*NOT A CONSTANT*)") END;
				END;
			END;
		END VisitConstant;

		PROCEDURE ConstantList(x: SyntaxTree.Constant);
		BEGIN
			Indent;  Keyword("CONST " );
			w.IncIndent;
			WHILE(x # NIL) DO
				Indent;
				VisitConstant(x);
				w.String( "; " );
				x := x.nextConstant;
			END;
			w.DecIndent;
		END ConstantList;

		PROCEDURE VisitVariable(x: SyntaxTree.Variable);
		BEGIN
			IF Visible(x) THEN
				IF (x.access # SyntaxTree.Hidden) THEN
					PrintSymbol(x);
					Flags(x.flags);
					w.String( ": " );
					Type(x.type);
				ELSIF mode>SourceCode THEN
					PrintSymbol(x);
				END
			END;
		END VisitVariable;

		PROCEDURE VariableList(x: SyntaxTree.Variable);
		VAR next: SyntaxTree.Variable;
		BEGIN
			w.IncIndent;
			WHILE(x # NIL) DO
				next := x.nextVariable;
				IF (x.access # SyntaxTree.Hidden) OR (mode > SourceCode) THEN
					Indent;
					PrintSymbol(x);
					WHILE(next # NIL) & (next.type = x.type) & ((next.access # SyntaxTree.Hidden) OR (mode > SourceCode)) DO
						w.String(", "); PrintSymbol(next);
						next := next.nextVariable;
					END;
					IF x.access # SyntaxTree.Hidden THEN
						w.String(": ");
						Type(x.type);
					ELSE
						w.String(": ");
						ShortType(x.type);
					END;
					w.String("; ");
				END;
				x := next;
			END;
			w.DecIndent
		END VariableList;

		PROCEDURE VisitParameter(x: SyntaxTree.Parameter);
		BEGIN
			IF (x.access # SyntaxTree.Hidden) THEN
				IF x.kind = SyntaxTree.VarParameter THEN Keyword("VAR " );
				ELSIF x.kind = SyntaxTree.ConstParameter THEN Keyword("CONST " );
				END;
				PrintSymbol(x);
				w.String( ": " );
				Type(x.type);
			ELSIF (mode > SourceCode) THEN
				PrintSymbol(x);
			END;
		END VisitParameter;

		PROCEDURE ParameterList*(x: SyntaxTree.Parameter);
		VAR next: SyntaxTree.Parameter; first: BOOLEAN;
		BEGIN
			first := TRUE;
			w.String( "(" );
			WHILE(x # NIL) DO
				next := x.nextParameter;
				IF (x.access # SyntaxTree.Hidden) OR (mode > SourceCode) THEN
					IF ~first THEN w.String("; ") END;
					first := FALSE;
					IF x.kind = SyntaxTree.VarParameter THEN Keyword("VAR " );
					ELSIF x.kind = SyntaxTree.ConstParameter THEN Keyword("CONST " );
					END;
					PrintSymbol(x);
					WHILE (next # NIL) & (next.type = x.type) & (next.kind = x.kind) & ((next.access # SyntaxTree.Hidden) OR (mode > SourceCode)) DO
						w.String(", "); PrintSymbol(next);
						next := next.nextParameter;
					END;
					IF x.access # SyntaxTree.Hidden THEN
						w.String(": ");
						Type(x.type);
					ELSE
						w.String(": ");
						ShortType(x.type);
					END;
				END;
				x := next;
			END;
			w.String( ")" );
		END ParameterList;

		PROCEDURE Access(access: SET);
		BEGIN
			IF SyntaxTree.PublicWrite IN access THEN w.String(" PublicWrite") END;
			IF SyntaxTree.ProtectedWrite IN access THEN w.String(" ProtectedWrite") END;
			IF SyntaxTree.InternalWrite IN access THEN w.String(" InternalWrite") END;
			IF SyntaxTree.PublicRead IN access THEN w.String(" PublicRead") END;
			IF SyntaxTree.ProtectedRead IN access THEN w.String(" ProtectedRead") END;
			IF SyntaxTree.InternalRead IN access THEN w.String(" InternalRead") END;
		END Access;

		PROCEDURE VisitProcedure(x: SyntaxTree.Procedure);
		VAR type: SyntaxTree.ProcedureType;  flags: SET;
		BEGIN
			IF Visible(x) THEN
				Indent;  Keyword("PROCEDURE " );
				Modifiers(x.type(SyntaxTree.ProcedureType).flagList);
				(*
				CallingConvention(x.type(SyntaxTree.ProcedureType).callingConvention);
				*)
				type := x.type(SyntaxTree.ProcedureType);
				flags := type.flags;
				IF SyntaxTree.InlineFlag IN flags  THEN w.String(" - ") END;
				IF SyntaxTree.ConstructorFlag IN flags THEN w.String(" & ") END;
				IF (SyntaxTree.RealtimeFlag IN flags) & (x.type(SyntaxTree.ProcedureType).flagList = NIL)  THEN w.String("{REALTIME}") END;
				PrintSymbol(x);
				IF (type.firstParameter # NIL)  OR (type.returnType # NIL ) THEN  (* print parentheses only if not parameterless procedure *)
					ParameterList(type.firstParameter);
				END;
				IF type.returnType # NIL THEN
					w.String( ": " );
					Type(type.returnType);
				END;
				IF info & (type.returnParameter # NIL) THEN
					BeginComment;
					VisitParameter(type.returnParameter);
					EndComment;
				END;
				w.String( ";" );
				IF mode >= SymbolFile THEN
					ProcedureScope(x.procedureScope);
				END;
				Indent;  Keyword("END " );  Identifier(x.name);
			END;
		END VisitProcedure;

		PROCEDURE VisitOperator(x: SyntaxTree.Operator);
		VAR type: SyntaxTree.ProcedureType;
		BEGIN
			IF Visible(x) THEN
				Indent;
				Keyword("OPERATOR ");
				type := x.type(SyntaxTree.ProcedureType);
				PrintSymbol(x);
				ParameterList(type.firstParameter);
				IF type.returnType # NIL THEN
					w.String( ": " );
					Type(type.returnType);
				END;
				w.String( ";" );
				IF mode >= SymbolFile THEN
				ProcedureScope(x.procedureScope);
				END;
				Indent;  Keyword("END " );  	w.String( '"' );  Identifier(x.name);  w.String( '"' );
			END
		END VisitOperator;

		PROCEDURE ProcedureList(x: SyntaxTree.Procedure);
		BEGIN
			WHILE(x # NIL) DO
				IF (x.access # SyntaxTree.Hidden) & ~(SyntaxTree.BodyProcedureFlag IN x.flags) OR (mode > SourceCode)  THEN
					Symbol(x);
					w.String( "; " );
				END;
				x := x.nextProcedure;

				IF (x# NIL) & (mode > SymbolFile) & ((x.access # SyntaxTree.Hidden) OR (mode > SourceCode)) THEN w.Ln END;

			END;
		END ProcedureList;

		PROCEDURE VisitImport(x: SyntaxTree.Import);
		VAR context: SyntaxTree.Identifier;
		BEGIN
			IF x.moduleName # x.name THEN Identifier(x.name);  w.String( " := " );  END;
			IF x.module = NIL THEN AlertString("(*module = NIL*)");
			END;
			IF (x.scope = NIL) OR (x.scope.ownerModule = NIL) THEN context := NIL ELSE context := x.scope.ownerModule.context END;
			Identifier(x.moduleName);
			IF (x.context # NIL) & ~x.context.Equals(context) THEN
				w.String(" IN ");
				Identifier(x.context)
			END;
		END VisitImport;

		PROCEDURE ImportList(x: SyntaxTree.Import);
		VAR first: BOOLEAN;
		BEGIN
			Indent;  Keyword("IMPORT " );
			first := TRUE;
			WHILE(x # NIL) DO
				IF x.direct OR (mode > SymbolFile) THEN
					IF ~first THEN w.String(", ") ELSE first := FALSE END;
					VisitImport(x);
				END;
				x := x.nextImport;
			END;
			w.String( ";" );
		END ImportList;

		PROCEDURE VisitBuiltin(x: SyntaxTree.Builtin);
		BEGIN
			Indent; Keyword("BUILTIN ");
			Identifier(x.name);
		END VisitBuiltin;

		PROCEDURE BuiltinList(x: SyntaxTree.Builtin);
		BEGIN
			WHILE(x # NIL) DO
				VisitBuiltin(x);
				x := x.nextBuiltin;
			END;
		END BuiltinList;

		PROCEDURE Comment(x: SyntaxTree.Comment);
		VAR i: LONGINT; ch: CHAR;
		BEGIN
			Indent;
			IF x.prevSymbol # NIL THEN
				Identifier(x.prevSymbol.name); w.String(" < ");
			END;
			BeginComment;
			WHILE (i<LEN(x.source^)) & (x.source[i] #  0X) DO
				ch := x.source[i];
				IF ch = 0DX THEN w.Ln
				ELSE w.Char(ch)
				END;
				INC(i);
			END;
			EndComment;
			IF x.nextSymbol # NIL THEN
				w.String("< "); Identifier(x.nextSymbol.name);
			END;
		END Comment;

		PROCEDURE CommentList(x: SyntaxTree.Comment);
		BEGIN
			WHILE (x#NIL) DO
				Comment(x);
				x := x.nextComment;
			END;
		END CommentList;

		(*** scopes ****)

		PROCEDURE Scope*(x: SyntaxTree.Scope);
		VAR prevScope: SyntaxTree.Scope;
		BEGIN
			prevScope := currentScope;
			currentScope := x;
			w.IncIndent;
			(* ASSERT(currentScope.outerScope = prevScope); (* sanity check *) *)
			IF x.firstConstant # NIL THEN ConstantList(x.firstConstant); END;
			IF x.firstTypeDeclaration # NIL THEN TypeDeclarationList(x.firstTypeDeclaration); END;
			IF x.firstVariable # NIL THEN Indent;  Keyword("VAR " );  VariableList(x.firstVariable);  END;
			IF x.firstProcedure # NIL THEN w.Ln; ProcedureList(x.firstProcedure) END;
			w.DecIndent;
			currentScope := prevScope;
		END Scope;

		PROCEDURE ProcedureScope(x: SyntaxTree.ProcedureScope);
		VAR prevScope: SyntaxTree.Scope;
		BEGIN
			prevScope := currentScope;
			currentScope := x;
			IF (mode  >= SourceCode) THEN Scope(x) END;
			IF (mode >= SymbolFile) & (x.body # NIL) THEN Body(x.body)
			END;
			currentScope := prevScope;
		END ProcedureScope;


		PROCEDURE Statement*(x: SyntaxTree.Statement);
		BEGIN
			IF x = NIL THEN
				AlertString("nil statement")
			ELSE
				x.Accept(SELF)
			END
		END Statement;

		PROCEDURE StatementSequence(x: SyntaxTree.StatementSequence);
		VAR statement: SyntaxTree.Statement;  i: LONGINT;
		BEGIN
			IF singleStatement THEN
				w.String("...")
			ELSE
				FOR i := 0 TO x.Length() - 1 DO
					statement := x.GetStatement( i );
					Indent; Statement(statement);
					IF i < x.Length() - 1 THEN w.String( "; " );  END;
				END;
			END;
		END StatementSequence;

		PROCEDURE VisitStatement(x: SyntaxTree.Statement);
		BEGIN
			AlertString("InvalidStatement");
		END VisitStatement;

		PROCEDURE VisitProcedureCallStatement(x: SyntaxTree.ProcedureCallStatement);
		BEGIN Expression(x.call) END VisitProcedureCallStatement;

		PROCEDURE VisitAssignment(x: SyntaxTree.Assignment);
		BEGIN
			Expression(x.left); w.String( " := " );  Expression(x.right);
		END VisitAssignment;

		PROCEDURE IfPart(x: SyntaxTree.IfPart);
		BEGIN
	 		Keyword("IF " );
			Expression(x.condition);
			Keyword(" THEN " );
			w.IncIndent;
			StatementSequence(x.statements);
			w.DecIndent;
		END IfPart;

		PROCEDURE VisitIfStatement(x: SyntaxTree.IfStatement);
		VAR i: LONGINT;  elsif: SyntaxTree.IfPart;
		BEGIN
			IfPart(x.ifPart);
			FOR i := 0 TO x.ElsifParts() - 1 DO
				elsif := x.GetElsifPart( i );
				Indent; Keyword("ELS");
				IfPart(elsif);
			END;
			IF x.elsePart # NIL THEN
				Indent;  Keyword("ELSE" );
				w.IncIndent;
				StatementSequence(x.elsePart);
				w.DecIndent;
			END;
			Indent;  Keyword("END" );
		END VisitIfStatement;

		PROCEDURE VisitWithStatement(x: SyntaxTree.WithStatement);
		BEGIN
			Keyword("WITH " );
			Expression(x.variable);
			w.String(" : ");
			Expression(x.type);
			Keyword(" DO " );
			w.IncIndent;  StatementSequence(x.statements);  w.DecIndent;
			Indent; Keyword("END" );
		END VisitWithStatement;

		PROCEDURE CasePart(x: SyntaxTree.CasePart);
		VAR case: SyntaxTree.CaseConstant;
		BEGIN
			ExpressionList(x.elements);
			IF info THEN
				w.BeginComment;
				case := x.firstConstant;
				WHILE(case # NIL) DO
					IF case # x.firstConstant THEN w.String(",") END;
					w.Int(case.min,1); w.String(".."); w.Int(case.max,1);
					case := case.next;
				END;
				EndComment;
			END;
			w.String( ":" );  w.IncIndent; StatementSequence(x.statements);  w.DecIndent;
		END CasePart;

		PROCEDURE VisitCaseStatement(x: SyntaxTree.CaseStatement);
		VAR i: LONGINT;  case: SyntaxTree.CasePart;
		BEGIN
			Keyword("CASE " );
			Expression(x.variable);
			Keyword(" OF " );
			FOR i := 0 TO x.CaseParts() - 1 DO
				case := x.GetCasePart( i );
				Indent;
				w.String( "| " );
				CasePart(case);
			END;
			IF x.elsePart # NIL THEN
				Indent;
				Keyword("ELSE" );
				w.IncIndent;
				StatementSequence(x.elsePart);
				w.DecIndent;
			END;
			Indent;
			Keyword("END" );
		END VisitCaseStatement;

		PROCEDURE VisitWhileStatement(x: SyntaxTree.WhileStatement);
		BEGIN
			Keyword(" WHILE " );
			Expression(x.condition);
			Keyword(" DO " );
			w.IncIndent;
			StatementSequence(x.statements);
			w.DecIndent;
			Indent;
			Keyword("END" );
		END VisitWhileStatement;

		PROCEDURE VisitRepeatStatement(x: SyntaxTree.RepeatStatement);
		BEGIN
			Keyword(" REPEAT " );
			w.IncIndent;
			StatementSequence(x.statements);
			w.DecIndent;
			Indent;  Keyword("UNTIL " );
			Expression(x.condition);
		END VisitRepeatStatement;

		PROCEDURE VisitForStatement(x: SyntaxTree.ForStatement);
		BEGIN
			Keyword(" FOR " );
			Expression(x.variable);
			w.String( " := " );
			Expression(x.from);
			Keyword(" TO " );
			Expression(x.to);
			IF x.by # NIL THEN
				Keyword(" BY " );
				Expression(x.by);
			END;
			Keyword(" DO " );
			w.IncIndent;
			StatementSequence(x.statements);
			w.DecIndent;
			Indent;
			Keyword("END" );
		END VisitForStatement;

		PROCEDURE VisitLoopStatement(x: SyntaxTree.LoopStatement);
		BEGIN
			Keyword(" LOOP " );
			w.IncIndent;  StatementSequence(x.statements);  w.DecIndent;
			Indent;  Keyword("END" );
		END VisitLoopStatement;

		PROCEDURE VisitExitStatement(x: SyntaxTree.ExitStatement);
		BEGIN 	Keyword("EXIT" ) END VisitExitStatement;

		PROCEDURE VisitReturnStatement(x: SyntaxTree.ReturnStatement);
		BEGIN
			Keyword("RETURN " );
			IF x.returnValue # NIL THEN Expression(x.returnValue) END
		END VisitReturnStatement;

		PROCEDURE VisitAwaitStatement(x: SyntaxTree.AwaitStatement);
		BEGIN
			Keyword("AWAIT (" );  Expression(x.condition);  w.String( ")" );
		END VisitAwaitStatement;

		PROCEDURE Modifiers(x: SyntaxTree.Modifier);
		VAR name: Scanner.StringType; first: BOOLEAN;
		BEGIN
			first := TRUE;
			WHILE x # NIL DO
				IF first THEN w.String("{"); first := FALSE ELSE w.String(", ") END;
				x.identifier.GetString(name);
				w.String(name);
				IF x.expression # NIL THEN
					w.String("(");
					Expression(x.expression);
					w.String(")");
				END;
				x := x.nextModifier;
			END;
			IF ~first THEN w.String("} ") END;
		END Modifiers;

		(*
		PROCEDURE BlockModifier(x: SyntaxTree.StatementBlock);
		VAR first: BOOLEAN;
			PROCEDURE Comma;
			BEGIN
				IF first THEN first := FALSE ELSE w.String(", "); END;
			END Comma;
		BEGIN
			first := TRUE;
				IF x.flags # {} THEN
					w.String("{");
					IF SyntaxTree.ActiveFlag IN x.flags THEN Comma; w.String("ACTIVE") END;
					IF SyntaxTree.PriorityFlag IN x.flags THEN Comma; w.String("PRIORITY("); Expression(x(SyntaxTree.Body).priority); w.String(")"); first := FALSE; END;
					IF SyntaxTree.SafeFlag IN x.flags THEN Comma; w.String("SAFE") END;
					IF SyntaxTree.ExclusiveFlag IN x.flags THEN Comma; w.String("EXCLUSIVE") END;
					w.String("}");
				END;
		END BlockModifier;
		*)

		PROCEDURE VisitStatementBlock(x: SyntaxTree.StatementBlock);
		BEGIN
			Indent; Keyword("BEGIN"); Modifiers(x.blockModifiers);
			w.IncIndent;
			IF x.statements # NIL THEN StatementSequence(x.statements);  END;
			w.DecIndent;
			Indent; Keyword("END");
		END VisitStatementBlock;

		PROCEDURE Code(x: SyntaxTree.Code);
		VAR  i: LONGINT; ch: CHAR; cr: BOOLEAN; size,value: LONGINT; procedure: SyntaxTree.Procedure;
		CONST CR=0DX;
		BEGIN
			IF currentScope # NIL THEN
				procedure := currentScope(SyntaxTree.ProcedureScope).ownerProcedure;
			END;
			IF (mode >= SourceCode) OR (procedure = NIL) OR (procedure.access * SyntaxTree.Public # {}) & procedure.HasFlag(SyntaxTree.InlineFlag) THEN
				IF (x.sourceCode # NIL) THEN
					i := 0;
					ch := x.sourceCode[0];
					WHILE (ch # 0X) DO
						IF ch = CR THEN
							cr := TRUE;
						ELSE
							IF cr THEN Indent; cr := FALSE END;
							w.Char(ch);
						END;
						INC(i); ch := x.sourceCode[i];
					END;
				END;
				(*
				IF x.inlineCode # NIL THEN
					w.String("; ");
					size := x.inlineCode.GetSize() DIV 8;
					FOR i := 0 TO size-1 DO
						value := x.inlineCode.GetBits(i*8,8);
						w.Hex(value,-2); w.String(" ");
					END;
				END;
				*)
			END;
		END Code;

		PROCEDURE VisitCode(x: SyntaxTree.Code);
		BEGIN
			Indent; Keyword("CODE");
			Code(x);
			Indent; Keyword("END");
		END VisitCode;

		PROCEDURE Body(x: SyntaxTree.Body);
		VAR
		BEGIN
			IF x.code # NIL THEN
				Indent; Keyword("CODE");
				Code(x.code);
			ELSE
				Indent;  Keyword("BEGIN" ); Modifiers(x.blockModifiers);
				IF mode >= SourceCode THEN
					IF x.statements # NIL THEN
						w.IncIndent;
						StatementSequence(x.statements);
						w.DecIndent;
					END;
					IF x.finally # NIL THEN
						Indent;  Keyword("FINALLY" );
						w.IncIndent;
						StatementSequence(x.finally);
						w.DecIndent
					END;
				END;
			END;
			(* "END" written by caller *)
		END Body;

		PROCEDURE Module*(x: SyntaxTree.Module);
		BEGIN
			IF x = NIL THEN
				AlertString("(* no module *)");
			ELSE
				case := x.case;
				currentScope := x.moduleScope.outerScope;
				Keyword("MODULE ");
				Identifier(x.name);
				IF (x.context # NIL) & (~x.context.Equals(Global.A2Name)) THEN
					w.String(" IN ");
					Identifier(x.context)
				END;
				w.String(";");
				w.IncIndent;
				IF x.moduleScope.firstImport # NIL THEN
					ImportList(x.moduleScope.firstImport)
				END;
				w.DecIndent;
				Scope(x.moduleScope);
				IF x.moduleScope.firstBuiltin # NIL THEN
					BuiltinList(x.moduleScope.firstBuiltin)
				END;

				IF (x.moduleScope.bodyProcedure # NIL) & (x.moduleScope.bodyProcedure.procedureScope.body # NIL) THEN
					Body(x.moduleScope.bodyProcedure.procedureScope.body)
				END;
				Indent; Keyword("END "); Identifier(x.name); w.String( "." ); w.Ln;  w.Update;

				IF (mode > SourceCode) & (x.moduleScope.firstComment # NIL) THEN w.Ln; CommentList(x.moduleScope.firstComment) END;

			END
		END Module;

		PROCEDURE SingleStatement*(b: BOOLEAN);
		BEGIN singleStatement := b
		END SingleStatement;

		PROCEDURE &Init(w: Streams.Writer; mode: LONGINT; info: BOOLEAN);
		BEGIN
			NEW(SELF.w,w);
			SELF.mode := mode; NEW(ws,128); SELF.info := info; case := Scanner.Uppercase;
			commentCount := 0; alertCount := 0; singleStatement := FALSE;
		END Init;

	END Printer;


(* debugging helper *)
VAR
	debug: Printer;

	PROCEDURE NewPrinter*(w: Streams.Writer; mode: LONGINT; info: BOOLEAN): Printer;
	VAR p: Printer;
	BEGIN
		NEW(p,w,mode,info); RETURN p
	END NewPrinter;


	PROCEDURE Info*(CONST info: ARRAY OF CHAR; a: ANY);
	VAR symbol: SyntaxTree.Symbol; scope: SyntaxTree.Scope;
	BEGIN
		NEW(debug.w,D.Log);
		D.Ln;
		D.Str(" --------> ");
		D.Str(info);
		D.Str(" ");
		D.Hex(SYSTEM.VAL(LONGINT,a),8);
		D.Str(" : ");

		IF a = NIL THEN
			D.Str("NIL");
		ELSIF a IS SyntaxTree.Expression THEN
			debug.Expression(a(SyntaxTree.Expression));
			Info("with type",a(SyntaxTree.Expression).type);
		ELSIF a IS SyntaxTree.Type THEN
			IF a IS SyntaxTree.QualifiedType THEN
				D.Str("[QualifiedType] ");
			END;
			debug.Type(a(SyntaxTree.Type))
		ELSIF a IS SyntaxTree.Symbol THEN
			debug.Symbol(a(SyntaxTree.Symbol))
		ELSIF a IS SyntaxTree.Statement THEN
			debug.Statement(a(SyntaxTree.Statement))
		ELSIF a IS SyntaxTree.Scope THEN
			scope := a(SyntaxTree.Scope);
			WHILE(scope # NIL) DO
				D.Ln; 		D.Str("      ");
				IF scope IS SyntaxTree.ModuleScope THEN D.Str("ModuleScope: ")
				ELSIF scope IS SyntaxTree.ProcedureScope THEN D.Str("ProcedureScope: ");
				ELSIF scope IS SyntaxTree.RecordScope THEN D.Str("RecordScope: ");
				ELSE D.Str("Scope: ");
				END;
				symbol := scope.firstSymbol;
				WHILE(symbol # NIL) DO
					debug.Identifier(symbol.name); D.Str(" ");
					symbol := symbol.nextSymbol;
				END;
				scope := scope.outerScope;
			END;
		ELSIF a IS SyntaxTree.Identifier THEN
			debug.Identifier(a(SyntaxTree.Identifier));
		ELSIF a IS SyntaxTree.QualifiedIdentifier THEN
			debug.QualifiedIdentifier(a(SyntaxTree.QualifiedIdentifier));
		ELSIF a IS SyntaxTree.Module THEN
			debug.Module(a(SyntaxTree.Module))
		ELSE
			debug.w.String("unknown");
		END;
		D.Update();
	END Info;


	PROCEDURE Init;
	BEGIN
		NEW(debug,D.Log,All,TRUE);
		debug.case := Scanner.Uppercase;
	END Init;

BEGIN
	Init;
END OCPrintout.
