MODULE FoxIntermediateScanner;

IMPORT
  Fs := FoxScanner,
  Streams,
  Diagnostics,
  Basic := FoxBasic,
  Commands,
  D := Debugging;

CONST
  Trace = TRUE;

  TAB   = 09X;

  TK_None*              =   0;

  TK_Module*            =   1;
  TK_Imports*           =   2;
  TK_Bodycode*          =   3;
  TK_Inlinecode*        =   4;
  TK_Initcode*          =   5;
  TK_Var*               =   6;
  TK_Const*             =   7;
  TK_Code*              =   8;
  TK_Offset*            =   9;

  TK_Reserve*           =  10;
  TK_Data*              =  11;

  TK_Nop*               =  12;
  TK_Mov*               =  13;
  TK_Conv*              =  14;
  TK_Call*              =  15;
  TK_Enter*             =  16;
  TK_Leave*             =  17;
  TK_Return*            =  18;
  TK_Exit*              =  19;
  TK_Result*            =  20;
  TK_Trap*              =  21;
  TK_Br*                =  22;
  TK_Breq*              =  23;
  TK_Brne*              =  24;
  TK_Brlt*              =  25;
  TK_Brge*              =  26;
  TK_Push*              =  27;
  TK_Not*               =  28;
  TK_Neg*               =  29;
  TK_Abs*               =  30;
  TK_Mul*               =  31;
  TK_Div*               =  32;
  TK_Mod*               =  33;
  TK_Sub*               =  34;
  TK_Add*               =  35;
  TK_And*               =  36;
  TK_Or*                =  37;
  TK_Xor*               =  38;
  TK_Shl*               =  39;
  TK_Shr*               =  40;
  TK_Rol*               =  41;
  TK_Ror*               =  42;
  TK_Copy*              =  43;
  TK_Fill*              =  44;
  TK_Asm*               =  45;

  TK_Sp*                =  46;
  TK_Fp*                =  47;

  TK_Comma*             =  48;
  TK_Becomes*           =  49;
  TK_LeftBracket*       =  50;
  TK_RightBracket*      =  51;
  TK_Hash*              =  52;
  TK_LeftParenthesis*   =  53;
  TK_RightParenthesis*  =  54;
  TK_Colon*             =  55;
  TK_Dollar*            =  56;
  TK_At*                =  57;

  TK_Comment*           =  58;
  TK_String*            =  59;
  TK_Ln*                =  60;
  TK_Identifier*        =  61;
  TK_Number*            =  62;
  TK_Character*         =  63;
  TK_End*               =  64;
  TK_Minus*             =  65;
  TK_Plus*              =  66;

  TK_EndOfText*         =  67;

  NumberOfToken         =  68;

TYPE
  AssemblerScanner* = OBJECT
  VAR
    (* helper state information *)
    source-           : Fs.StringType;
    reader-           : Streams.Reader;   (* source *)
    diagnostics       : Diagnostics.Diagnostics;   (* error logging *)

    ch*               : CHAR;   (* look-ahead character *)
    position*         : LONGINT;   (* current position *)

    error-            : BOOLEAN;   (* IF error occured during scanning *)

    sourceWriter      : Streams.Writer;
    sourceString      : Fs.StringMaker;


    readerOrgPos      : LONGINT;
    startPosition     : LONGINT;
    reservedCharacter : ARRAY 256 OF BOOLEAN;
    tokens-           : ARRAY NumberOfToken OF Fs.Keyword;
    keywords          : Fs.KeywordTable;

  PROCEDURE & InitializeScanner*( CONST source: ARRAY OF CHAR; reader: Streams.Reader; position: LONGINT; diagnostics: Diagnostics.Diagnostics );
  BEGIN
    SELF.startPosition := position;
    SELF.readerOrgPos  := reader.Pos();
    NEW(sourceString,1024);
    sourceWriter := sourceString.GetWriter();
    error := FALSE;
    COPY (source, SELF.source);
    SELF.reader := reader;
    SELF.diagnostics := diagnostics;
    ch := " ";
    IF reader = NIL THEN ch := Fs.EOT ELSE GetNextCharacter END;
    IF Trace THEN D.Str( "New scanner  " );   D.Ln;  END;
    SELF.position := position;
    InitKeywords();
    InitTokens();
    InitReservedCharacters();
  END InitializeScanner;

  PROCEDURE Error( code: INTEGER );
  VAR
    errorMessage: ARRAY 256 OF CHAR;
  BEGIN
    IF diagnostics # NIL THEN
      Basic.GetErrorMessage(code,"",errorMessage);
      diagnostics.Error(source, position, code, errorMessage)
    END;
    error := TRUE;
  END Error;

  PROCEDURE Reset*;
  BEGIN
    reader.SetPos(readerOrgPos);
    ch := " ";
    IF reader = NIL THEN
      ch := Fs.EOT;
    ELSE
      GetNextCharacter;
    END;
    position := startPosition;
  END Reset;

  PROCEDURE SkipToEndOfLine*;
  BEGIN
    WHILE (ch # Fs.EOT) & (ch # Fs.CR) & (ch # Fs.LF) DO
      GetNextCharacter;
    END;
  END SkipToEndOfLine;

  PROCEDURE GetNextCharacter;
  BEGIN
    ASSERT(ch # Fs.EOT);
    reader.Char(ch);
    INC(position);
    (*
    (* not necessary, as Streams returns 0X IF reading failed, but in case Streams.Reader.Char is modified ...  *)
    IF reader.res # Streams.Ok THEN ch := EOT END;
    *)
  END GetNextCharacter;

  (** get a string starting at current position
    string = '"' {(Character-'"') | '\"'} '"'.
  **)
  PROCEDURE GetString(VAR symbol: Fs.Symbol);
  VAR
    i       : INTEGER;
  BEGIN
    i       := 0;
    LOOP
      GetNextCharacter;
      IF ch = '\' THEN
        GetNextCharacter;
        CASE ch OF
        | '"':
          ch := '"';
        | '\':
          ch := '\';
        | 'n':
          ch := Fs.LF;
        | 't':
          ch := TAB;
        ELSE
          Error( Basic.StringIllegalCharacter );
          EXIT;
        END;
      ELSE
        IF ch = '"' THEN
          EXIT;
        END;
      END;
      IF i = Fs.MaxStringLength - 1 THEN    (*TODO: length 256 is not enough*)
        Error( Basic.StringTooLong );
        EXIT;
      END;
      symbol.string[i] := ch;
      INC( i );
    END;
    GetNextCharacter;
    symbol.string[i]    := 0X;
    symbol.character    := symbol.string[0];
    symbol.stringLength := i + 1;
  END GetString;

  (**
    Identifier = Letter {Letter | Digit | '_'} .
    Letter = 'A' | 'B' | .. |  'Z' | 'a' | 'b' |  .. | 'z' .
    Digit = '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'.

    '_' is the underscore character
  **)
  PROCEDURE GetIdentifier( VAR symbol: Fs.Symbol );
  VAR
    i: LONGINT;
  BEGIN
    i := 0;
    REPEAT
      symbol.string[i] := ch;
       INC( i );
      GetNextCharacter
    UNTIL reservedCharacter[ORD( ch )] OR (i = Fs.MaxIdentifierLength);
    IF i = Fs.MaxIdentifierLength THEN Error( Basic.IdentifierTooLong );  DEC( i ) END;
    symbol.string[i] := 0X;
  END GetIdentifier;

  (**
  Number       =  Integer | Real.
  Integer      =  Digit {Digit} | Digit {HexDigit} 'H'.
  Real         =  Digit {Digit} '.' {Digit} [ScaleFactor].
  ScaleFactor  =  ('E' | 'D') ['+' | '-'] digit {digit}.
  HexDigit     =  Digit | 'A' | 'B' | 'C' | 'D' | 'E' | 'F'.
  Digit = '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' .
  **)
  PROCEDURE GetNumber(VAR symbol: Fs.Symbol): Fs.Token;
  VAR i, nextInt, m, n, d, e, si: LONGINT;
    dig: ARRAY 24 OF CHAR;
    f: LONGREAL;  expCh: CHAR;  neg, long: BOOLEAN;
    result: LONGINT;
    hugeint, tenh: HUGEINT;

    (** 10^e **)
    PROCEDURE Ten( e: LONGINT ): LONGREAL;
    VAR x, p: LONGREAL;
    BEGIN
      x := 1;  p := 10;
      WHILE e > 0 DO
        IF ODD( e ) THEN x := x * p END;
        e := e DIV 2;
        IF e > 0 THEN p := p * p END  (* prevent overflow *)
      END;
      RETURN x
    END Ten;

    (** RETURN decimal number associated to character ch , error IF none **)
    PROCEDURE Decimal( ch: CHAR ): LONGINT;
    BEGIN  (* ("0" <= ch) & (ch <= "9") or ("A" <= ch) & (ch <= "F") *)
      IF ch <= "9" THEN RETURN ORD( ch ) - ORD( "0" ) ELSE Error( Basic.NumberIllegalCharacter );  RETURN 0 END
    END Decimal;

    (** RETURN hexadecimal number associated to character ch, error IF none **)
    PROCEDURE Hexadecimal( ch: CHAR ): LONGINT;
    BEGIN
      IF ch <= "9" THEN RETURN ORD( ch ) - ORD( "0" )
      ELSIF ch <= "F" THEN RETURN ORD( ch ) - ORD( "A" ) + 10
      ELSE Error( Basic.NumberIllegalCharacter );  RETURN 0
      END
    END Hexadecimal;

  BEGIN  (* ("0" <= ch) & (ch <= "9") *)
    result := TK_Number;
    i := 0;  m := 0;  n := 0;  d := 0;  si := 0;  long := FALSE;
    LOOP  (* read mantissa *)
      IF ("0" <= ch) & (ch <= "9") OR (d = 0) & ("A" <= ch) & (ch <= "F") THEN
        IF (m > 0) OR (ch # "0") THEN  (* ignore leading zeros *)
          IF n < LEN( dig ) THEN dig[n] := ch;  INC( n ) END;
          INC( m )
        END;
        symbol.string[si] := ch;  INC( si );  GetNextCharacter;  INC( i )
      ELSIF ch = "." THEN
        symbol.string[si] := ch;  INC( si );  GetNextCharacter;
        IF ch = "." THEN (*ch := Ellipsis;  EXIT*)
        ELSIF d = 0 THEN  (* i > 0 *) d := i
        ELSE Error( Basic.NumberIllegalCharacter )
        END
      ELSE EXIT
      END
    END;   (* 0 <= n <= m <= i, 0 <= d <= i *)
    IF d = 0 THEN  (* integer *)
      IF n = m THEN
        symbol.integer := 0;  i := 0;  symbol.hugeint := 0;
        IF ch = "X" THEN  (* character *)
          symbol.string[si] := ch;  INC( si );  GetNextCharacter;  result := TK_Character;
          IF  (n <= 2) THEN
            WHILE i < n DO symbol.integer := symbol.integer * 10H + Hexadecimal( dig[i] );  INC( i ) END;
            symbol.character := CHR(symbol.integer);
          ELSE Error( Basic.NumberTooLarge )
          END
        ELSIF ch = "H" THEN  (* hexadecimal *)
          symbol.string[si] := ch;  INC( si );  GetNextCharacter;
          IF (n < Fs.MaxHexDigits) OR (n=Fs.MaxHexDigits) & (dig[0] <= "7")  THEN (* otherwise the positive (!) number is not in the range OF longints *)
            symbol.numberType := Fs.Integer;
            (* IF (n = MaxHexDigits) & (dig[0] > "7") THEN  (* prevent overflow *) symbol.integer := -1 END;  *)
            WHILE i < n DO symbol.integer := symbol.integer * 10H + Hexadecimal( dig[i] );  INC( i ) END
          ELSIF n <= Fs.MaxHugeHexDigits THEN
            symbol.numberType := Fs.Hugeint;
            IF (n = Fs.MaxHugeHexDigits) & (dig[0] > "7") THEN  (* prevent overflow *) symbol.hugeint := -1 END;
            WHILE i < n DO symbol.hugeint := Hexadecimal( dig[i] ) + symbol.hugeint * 10H;  INC( i ) END
          ELSE
            symbol.numberType := Fs.Hugeint; (* to make parser able to go on *)
            Error( Basic.NumberTooLarge )
          END
        ELSE  (* decimal *)
          symbol.numberType := Fs.Integer;
          WHILE (i < n) & ~long  DO
            d := Decimal( dig[i] );  INC( i );
            nextInt := symbol.integer*10+d;
            IF nextInt >=0 THEN symbol.integer := nextInt ELSE (* overflow *) long := TRUE END;
          END;
          IF long THEN
            i := 0; (* restart computation , artificial limit because OF compiler problems with hugeint *)
            hugeint := 0;
            tenh := 10; (* compiler does not like constants here ! *)
            symbol.numberType := Fs.Hugeint;
            WHILE i < n DO
              d := Decimal( dig[i] );  INC( i );
              hugeint := hugeint * tenh + d;
              IF hugeint < 0 THEN Error( Basic.NumberTooLarge ) END
            END;
            symbol.hugeint := hugeint;
          END
        END
      ELSE
        symbol.numberType := Fs.Hugeint;
        Error( Basic.NumberTooLarge )
      END
    ELSE  (* fraction *)
      f := 0;  e := 0;  expCh := "E";
      WHILE n > 0 DO  (* 0 <= f < 1 *) DEC( n );  f := (Decimal( dig[n] ) + f) / 10 END;
      IF (ch = "E") OR (ch = "D") THEN
        expCh := ch;  symbol.string[si] := ch;  INC( si );  GetNextCharacter;  neg := FALSE;
        IF ch = "-" THEN neg := TRUE;  symbol.string[si] := ch;  INC( si );  GetNextCharacter
        ELSIF ch = "+" THEN symbol.string[si] := ch;  INC( si );  GetNextCharacter
        END;
        IF ("0" <= ch) & (ch <= "9") THEN
          REPEAT
            n := Decimal( ch );  symbol.string[si] := ch;  INC( si );  GetNextCharacter;
            IF e <= (MAX( INTEGER ) - n) DIV 10 THEN e := e * 10 + n ELSE Error( Basic.NumberTooLarge ) END
          UNTIL (ch < "0") OR ("9" < ch);
          IF neg THEN e := -e END
        ELSE Error( Basic.NumberIllegalCharacter )
        END
      END;
      DEC( e, i - d - m );   (* decimal point shift *)
      IF expCh = "E" THEN
        symbol.numberType := Fs.Real;
        IF (1 - Fs.MaxRealExponent < e) & (e <= Fs.MaxRealExponent) THEN
          IF e < 0 THEN symbol.real :=  f / Ten( -e ) ELSE symbol.real := f * Ten( e )  END
        ELSE Error( Basic.NumberTooLarge )
        END
      ELSE
        symbol.numberType := Fs.Longreal;
        IF (1 - Fs.MaxLongrealExponent < e) & (e <= Fs.MaxLongrealExponent) THEN
          IF e < 0 THEN symbol.real := f / Ten( -e ) ELSE symbol.real := f * Ten( e ) END
        ELSE Error( Basic.NumberTooLarge )
        END
      END
    END;
    symbol.string[si] := 0X;
    RETURN result;
  END GetNumber;

  PROCEDURE SkipBlanks;
  BEGIN
    WHILE (ch <= " ") & (ch # Fs.EOT) DO
      GetNextCharacter
    END;
  END SkipBlanks;

  PROCEDURE GetNextSymbol*(VAR symbol: Fs.Symbol ): BOOLEAN;
  VAR
    s, token: LONGINT;
  BEGIN
    REPEAT
      SkipBlanks;
      symbol.start     := position;
      symbol.string[0] := ch;
      symbol.string[1] := 0X;
      CASE ch OF  (* ch > " " *)
      | Fs.EOT:
          s := TK_EndOfText;
      | Fs.DoubleQuote:
          GetString(symbol);
          s := TK_String;
      | "(":
          GetNextCharacter;
          s := TK_LeftParenthesis;
      | ")":
          GetNextCharacter;
          s := TK_RightParenthesis;
      | ",":
          GetNextCharacter;
          s := TK_Comma;
      | "0".."9":
          s := GetNumber(symbol);
      | ":":
          GetNextCharacter;
          s := TK_Colon;
      | ";":
          SkipToEndOfLine;
          s := TK_Comment;
      | "=":
          GetNextCharacter;
          s := TK_Becomes;
      | "[":
          GetNextCharacter;
          s := TK_LeftBracket;
      | "]":
          GetNextCharacter;
          s := TK_RightBracket;
      | '$':
          GetNextCharacter;
          s := TK_Dollar;
      | '@':
          GetNextCharacter;
          s := TK_At;
      | '-':
          GetNextCharacter;
          s := TK_Minus;
      | '+':
          GetNextCharacter;
          s := TK_Plus;
      | "a".."z", "A".."Z":
          GetIdentifier( symbol);
          s := TK_Identifier;
          token := keywords.IndexByString(symbol.string);
          IF token >= 0 THEN
            s := token
          END;
      ELSE
        s := TK_None;
        GetNextCharacter;
      END;
      symbol.end := position;
    UNTIL s # TK_Comment;

    symbol.token := s;

    IF Trace THEN
      D.Ln;
(*      D.Str( "Scan at " );
      D.Int( symbol.start,1 );
      D.Str( ": " );*)
      OutSymbol(D.Log,symbol);
      D.Update;
    END;
    RETURN ~error
  END GetNextSymbol;

  PROCEDURE OutSymbol*(w: Streams.Writer; CONST symbol: Fs.Symbol);
  BEGIN
    w.Int(symbol.start,1);
    w.String("-");
    w.Int(symbol.end,1);
    w.String(":");
    w.String(tokens[symbol.token]);
    IF symbol.token= Fs.Number THEN
      CASE symbol.numberType OF
        Fs.Integer: w.String("(integer)")
        |Fs.Hugeint: w.String("(hugeint)")
        |Fs.Real: w.String("(real)")
        |Fs.Longreal: w.String("(longreal)")
      END;
    END;
    IF symbol.string # "" THEN w.String(": "); w.String('"'); w.String(symbol.string); w.String('"') END;
  END OutSymbol;


  (** reserved characters are the characters that may not occur within an identifier **)
  PROCEDURE InitReservedCharacters;
  VAR i: LONGINT;
  BEGIN
    FOR i := 0 TO LEN( reservedCharacter ) - 1 DO
      CASE CHR(i) OF
        | 'a' .. 'z', 'A' .. 'Z': reservedCharacter[i] := FALSE;
        | '0'..'9': reservedCharacter[i] := FALSE;
        | '_': reservedCharacter[i] := FALSE;
        | '.': reservedCharacter[i] := FALSE;
        | '@': reservedCharacter[i] := FALSE;
        | '$': reservedCharacter[i] := FALSE;
      ELSE
        reservedCharacter[i] := TRUE;
      END;
    END;
  END InitReservedCharacters;

  (* get keyword by token *)
  PROCEDURE GetKeyword*( token: LONGINT; VAR name: ARRAY OF CHAR);
  BEGIN
      keywords.StringByIndex(token,name);
  END GetKeyword;

  PROCEDURE InitTokens;
  VAR i: LONGINT;
  BEGIN
    tokens[TK_None]        := "None";

    tokens[TK_Module]      := "Module";
    tokens[TK_Imports]     := "Imports";
    tokens[TK_Bodycode]    := "Bodycode";
    tokens[TK_Inlinecode]  := "Inlinecode";
    tokens[TK_Initcode]    := "Initcode";
    tokens[TK_Var]         := "Var";
    tokens[TK_Const]       := "Const";
    tokens[TK_Code]        := "Code";
    tokens[TK_Offset]      := "Offset";

    tokens[TK_Reserve]     := "Reserve";

    tokens[TK_Data]        := "Data";

    tokens[TK_Nop]         := "Nop";
    tokens[TK_Mov]         := "Mov";
    tokens[TK_Conv]        := "Conv";
    tokens[TK_Call]        := "Call";
    tokens[TK_Enter]       := "Enter";
    tokens[TK_Leave]       := "Leave";
    tokens[TK_Return]      := "Return";
    tokens[TK_Exit]        := "Exit";
    tokens[TK_Result]      := "Result";
    tokens[TK_Trap]        := "Trap";
    tokens[TK_Br]          := "Br";
    tokens[TK_Breq]        := "Breq";
    tokens[TK_Brne]        := "Brne";
    tokens[TK_Brlt]        := "Brlt";
    tokens[TK_Brge]        := "Brge";
    tokens[TK_Push]        := "Push";
    tokens[TK_Not]         := "Not";
    tokens[TK_Neg]         := "Neg";
    tokens[TK_Abs]         := "Abs";
    tokens[TK_Mul]         := "Mul";
    tokens[TK_Div]         := "Div";
    tokens[TK_Mod]         := "Mod";
    tokens[TK_Sub]         := "Sub";
    tokens[TK_Add]         := "Add";
    tokens[TK_And]         := "And";
    tokens[TK_Or]          := "Or";
    tokens[TK_Xor]         := "Xor";
    tokens[TK_Shl]         := "Shl";
    tokens[TK_Shr]         := "Shr";
    tokens[TK_Rol]         := "Rol";
    tokens[TK_Ror]         := "Ror";
    tokens[TK_Copy]        := "Copy";
    tokens[TK_Fill]        := "Fill";
    tokens[TK_Asm]         := "Asm";

    tokens[TK_Sp]          := "Sp";
    tokens[TK_Fp]          := "Fp";

    tokens[TK_Comma]            := "Comma";
    tokens[TK_Becomes]          := "Becomes";
    tokens[TK_LeftBracket]      := "LeftBracket";
    tokens[TK_RightBracket]     := "RightBracket";
    tokens[TK_Hash]             := "Hash";
    tokens[TK_LeftParenthesis]  := "LeftParenthesis";
    tokens[TK_RightParenthesis] := "RightParenthesis";
    tokens[TK_Colon]            := "Colon";
    tokens[TK_Dollar]           := "Dollar";
    tokens[TK_At]               := "At";
    tokens[TK_Minus]            := "Minus";
    tokens[TK_Plus]             := "Plus";

    tokens[TK_EndOfText]        := "EndOfText";
    tokens[TK_Comment]          := "Comment";
    tokens[TK_String]           := "String";
    tokens[TK_Ln]               := "Ln";
    tokens[TK_Identifier]       := "Identifier";
    tokens[TK_Number]           := "Number";
    tokens[TK_Character]        := "Character";
    tokens[TK_End]              := "End";

    FOR i := 0 TO NumberOfToken-1 DO
      ASSERT(tokens[i] # "")
    END;
  END InitTokens;

  (** enter keywords in the list OF keywords (both upper- and lowercase)  **)
  PROCEDURE InitKeywords;
    PROCEDURE Enter(CONST name: ARRAY OF CHAR; token: LONGINT);
    BEGIN
      keywords.PutString(name,token);
      Basic.SetErrorExpected(token,name);
    END Enter;

    PROCEDURE EnterSymbol(CONST name: ARRAY OF CHAR; token: LONGINT);
    BEGIN
      Enter(name,token);
    END EnterSymbol;

  BEGIN
    NEW(keywords,NumberOfToken);

    (* header and sections *)
    Enter( "module",      TK_Module );
    Enter( "imports",     TK_Imports );

    Enter( "bodycode",    TK_Bodycode );
    Enter( "inlinecode",  TK_Inlinecode );
    Enter( "imports",     TK_Imports );
    Enter( "initcode",    TK_Initcode );
    Enter( "var",         TK_Var );
    Enter( "const",       TK_Const );
    Enter( "code",        TK_Code );

    Enter( "offset",      TK_Offset );

    (* var section *)
    Enter( "reserve",     TK_Reserve );

    (* const section *)
    Enter( "data",        TK_Data );

    (* code section *)
    Enter( "nop",         TK_Nop );
    Enter( "mov",         TK_Mov );
    Enter( "conv",        TK_Conv );
    Enter( "call",        TK_Call );
    Enter( "enter",       TK_Enter );
    Enter( "leave",       TK_Leave );
    Enter( "return",      TK_Return );
    Enter( "exit",        TK_Exit );
    Enter( "result",      TK_Result );
    Enter( "trap",        TK_Trap );
    Enter( "br",          TK_Br );
    Enter( "breq",        TK_Breq );
    Enter( "brne",        TK_Brne );
    Enter( "brlt",        TK_Brlt );
    Enter( "brge",        TK_Brge );
    Enter( "push",        TK_Push );
    Enter( "not",         TK_Not );
    Enter( "neg",         TK_Neg );
    Enter( "abs",         TK_Abs );
    Enter( "mul",         TK_Mul );
    Enter( "div",         TK_Div );
    Enter( "mod",         TK_Mod );
    Enter( "sub",         TK_Sub );
    Enter( "add",         TK_Add );
    Enter( "and",         TK_And );
    Enter( "or",          TK_Or );
    Enter( "xor",         TK_Xor );
    Enter( "shl",         TK_Shl );
    Enter( "shr",         TK_Shr );
    Enter( "rol",         TK_Rol );
    Enter( "ror",         TK_Ror );
    Enter( "copy",        TK_Copy );
    Enter( "fill",        TK_Fill );
    Enter( "asm",         TK_Asm );

    (* register *)
    Enter( "SP",          TK_Sp );
    Enter( "FP",          TK_Fp );

    (* symbols *)
    EnterSymbol( ",", TK_Comma );
    EnterSymbol( "=", TK_Becomes );
    EnterSymbol( "[", TK_LeftBracket );
    EnterSymbol( "]", TK_RightBracket );
    EnterSymbol( "#", TK_Hash );
    EnterSymbol( "(", TK_LeftParenthesis );
    EnterSymbol( ")", TK_RightParenthesis );
    EnterSymbol( ":", TK_Colon );
    EnterSymbol( "$", TK_Dollar );
    EnterSymbol( "@", TK_At );
    EnterSymbol( "-", TK_Minus );
    EnterSymbol( "+", TK_Plus );

    Basic.SetErrorMessage(TK_Number,"missing number");
    Basic.SetErrorMessage(TK_String,"missing string");
    Basic.SetErrorMessage(TK_Character,"missing character");
    Basic.SetErrorMessage(TK_Identifier,"missing identifier");
    END InitKeywords;


  (** debugging / reporting **)
  PROCEDURE ReportKeywords*(context: Commands.Context);
  VAR i: LONGINT; name: Fs.Keyword;
  BEGIN
    FOR i := 0 TO NumberOfToken-1 DO
      context.out.Int(i,1);
      context.out.String(": ");
      context.out.Char('"');
      keywords.StringByIndex(i,name);
      context.out.String(name);
      context.out.Char('"');
      context.out.Ln;
    END;
  END ReportKeywords;


  END AssemblerScanner;

  PROCEDURE NewAssemblerScanner*( CONST source: ARRAY OF CHAR; reader: Streams.Reader; position: LONGINT; diagnostics: Diagnostics.Diagnostics ): AssemblerScanner;
  VAR
    s: AssemblerScanner;
  BEGIN
    NEW( s, source, reader, position, diagnostics );
    RETURN s;
  END NewAssemblerScanner;

END FoxIntermediateScanner.

