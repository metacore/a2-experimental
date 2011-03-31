MODULE FoxOperatorRuntime;
IMPORT SYSTEM, Debugging; (* TENTATIVE *)
CONST
	AddressSize = SYSTEM.SIZEOF(SYSTEM.ADDRESS);
	MaxInheritanceDepth = 16;
	TypeTagsOffset = 2;
	
	MaxHashTableLoadFactor = 0.75;
	InitialHashTableSize = 64; (* TENTATIVE *)

	(* special pointer values *)
	NonPointer = -1;
	NilValue = 0;
	
	(* special type info values *)
	NoType = 0;
	
	(* for the operator kind *)
	LhsIsPointer = 0;
	RhsIsPointer = 1;
	
TYPE
	Key = RECORD
		identifier: LONGINT;
		kind: SET; (* which operands are pointers *)
		leftType, rightType: LONGINT; (* typetag for pointer to records, fingerprint otherwise. for unary operators 'rightType' is set to 'NoType' *)
	END;

	Value = SYSTEM.ADDRESS; (* the operator's address *)
	
	HashArray = POINTER TO ARRAY OF RECORD
		isOccupied: BOOLEAN;
		key: Key;
		value: Value;
	END;

	HashTable = OBJECT
	VAR
		table: HashArray;
		size: LONGINT;
		used: LONGINT;
		lastHashValue: LONGINT; (* optimization *)
		lastKey: Key;

		PROCEDURE & Init(initialSize: LONGINT);
		BEGIN
			ASSERT(initialSize > 2);
			NEW(table, initialSize);
			size := initialSize;
			used := 0
		END Init;

		PROCEDURE Put(key: Key; value: Value);
		VAR
			hashValue: LONGINT;
		BEGIN
			ASSERT(used < size);
			hashValue := HashValue(key);
			IF ~table[hashValue].isOccupied THEN
				INC(used)
			END;
			table[hashValue].isOccupied := TRUE;
			table[hashValue].key := key;
			table[hashValue].value := value;
									
			IF (used / size) > MaxHashTableLoadFactor THEN Grow END
		END Put;
		
		PROCEDURE Get(key: Key): Value;
		BEGIN
			RETURN table[HashValue(key)].value
		END Get;

		PROCEDURE Has(key: Key): BOOLEAN;
		VAR
			hashValue: LONGINT;
		BEGIN
			hashValue := HashValue(key);
			RETURN table[hashValue].isOccupied & (table[hashValue].key = key)
		END Has;

		PROCEDURE Length(): LONGINT;
		BEGIN
			RETURN used;
		END Length;

		PROCEDURE Clear;
		VAR
			i: LONGINT;
		BEGIN
			FOR i := 0 TO size - 1 DO
				table[i].isOccupied := FALSE
			END
		END Clear;

		PROCEDURE HashValue(key: Key): LONGINT;
		VAR
			value, h1, h2, i: LONGINT;
		BEGIN
			IF key # lastKey THEN
				(* TENTATIVE *)
				(*
				Debugging.Ln;
				Debugging.String("key:"); Debugging.Ln;
				Debugging.String("    kind: "); Debugging.Set(key.kind); Debugging.Ln;
				Debugging.String("    ID: "); Debugging.Int(key.identifier, 0); Debugging.Ln;
				Debugging.String("    left type: "); Debugging.Int(key.leftType, 0); Debugging.Ln;
				Debugging.String("    right type:"); Debugging.Int(key.rightType, 0); Debugging.Ln;
				Debugging.Ln;
				*)
				
				(* first, create integer value from key *)
				(* the operator kind is ignored for the hash *)
				value := SYSTEM.VAL(LONGINT,
						SYSTEM.VAL(SET, SYSTEM.ROT(key.identifier, 0)) /
						SYSTEM.VAL(SET, SYSTEM.ROT(key.leftType, 0)) /
						SYSTEM.VAL(SET, SYSTEM.ROT(key.rightType, 8))
						);
				
				(* second, calculated hash value for the integer *)
				h1 := value MOD size;
				h2 := 1; (* Linear probing *)
				i := 0;
				REPEAT
					value := (h1 + i * h2) MOD size;
					INC(i)
				UNTIL ~table[value].isOccupied OR (table[value].key = key) OR (i > size);
				
				ASSERT(~table[value].isOccupied OR (table[value].key = key));
				
				lastHashValue := value;
				lastKey := key
			END;
			RETURN lastHashValue
		END HashValue;

		PROCEDURE Grow;
		VAR
			oldTable: HashArray;
			oldSize, i: LONGINT;
		BEGIN
			oldSize := size;
			oldTable := table;
			Init(size * 2);
			FOR i := 0 TO oldSize - 1 DO
				IF oldTable[i].isOccupied THEN
					Put(oldTable[i].key, oldTable[i].value)
				END
			END
		END Grow;
	END HashTable;

VAR
	hashTable: HashTable;

	OPERATOR "="(left, right: Key): BOOLEAN;
	BEGIN
		RETURN (left.identifier = right.identifier) & (left.kind = right.kind) & (left.leftType = right.leftType) & (left.rightType = right.rightType)
	END "=";

	OPERATOR "#"(left, right: Key): BOOLEAN;
	BEGIN
		RETURN ~(left = right);
	END "#";

	(* TENTATIVE *)
	PROCEDURE DumpHashTable*;
	VAR
		i: LONGINT;
	BEGIN (* {EXCLUSIVE} *)
		Debugging.String("hash table:");
		Debugging.Ln;
		FOR i := 0 TO hashTable.size - 1 DO
			Debugging.String("    ");
			Debugging.Int(i, 0);
			Debugging.String(": ");
			IF hashTable.table[i].isOccupied THEN
				Debugging.String("(");
				Debugging.Int(hashTable.table[i].key.identifier, 0);
				Debugging.String(", ");
				Debugging.Set(hashTable.table[i].key.kind);
				Debugging.String(", ");
				Debugging.Int(hashTable.table[i].key.leftType, 0);
				Debugging.String(", ");
				Debugging.Int(hashTable.table[i].key.rightType, 0);
				Debugging.String(") -> ");
				Debugging.Int(hashTable.table[i].value, 0)
			ELSE
				Debugging.String("-")
			END;
			Debugging.Ln
		END;
		Debugging.Ln;
		Debugging.Update
	END DumpHashTable;
	
	(** determine the level of a type in the inheritance hierarchy (0 -> topmost supertype) **)
	PROCEDURE LevelOfType(type: SYSTEM.ADDRESS): SHORTINT;
	VAR
		result: SHORTINT;
		typeTag: SYSTEM.ADDRESS;
	BEGIN
		result := MaxInheritanceDepth;
		WHILE typeTag # type DO
			DEC(result);
			IF result < 0 THEN HALT(100) END; (* error: tag list does not include own type (should not occur) *)
			SYSTEM.GET(type - AddressSize * (TypeTagsOffset + result), typeTag)
		END;
		ASSERT((result >= 0) & (result < MaxInheritanceDepth));
		RETURN result
	END LevelOfType;
	
	(** get the type at a particular level in the inheritance hierarchy looking from a specific concrete type**)
	PROCEDURE TypeOfLevel(concreteType: SYSTEM.ADDRESS; level: LONGINT): SYSTEM.ADDRESS;
	VAR
		result: SYSTEM.ADDRESS;
	BEGIN
		ASSERT((level >= 0) & (level < MaxInheritanceDepth));
		SYSTEM.GET(concreteType - AddressSize * (TypeTagsOffset + level), result);
		RETURN result
	END TypeOfLevel;
	
	(** register an operator **)
	PROCEDURE RegisterOperator*(identifier: LONGINT; kind: SET; leftTypeInfo, rightTypeInfo: LONGINT; operatorAddress: SYSTEM.ADDRESS);
	VAR
		key: Key;
	BEGIN (* {EXCLUSIVE} *)
		ASSERT((LhsIsPointer IN kind) OR (RhsIsPointer IN kind));
		ASSERT(leftTypeInfo # NoType);
		IF rightTypeInfo = NoType THEN ASSERT(LhsIsPointer IN kind) END;
		
		Debugging.String(">>> register operator"); Debugging.Ln; (* TENTATIVE *)

		(* compose key *)
		key.identifier := identifier;
		key.kind := kind;
		key.leftType := leftTypeInfo;
		key.rightType := rightTypeInfo;
		
		hashTable.Put(key, operatorAddress)
	END RegisterOperator;

	(** get the address of an operator that specifically handles parameters of certain types
		(if polymorphic search is enabled, other signature-compatible operators are also taken into consideration)
	**)
	PROCEDURE SelectOperator*(identifier, leftPointer, leftTypeInfo, rightPointer, rightTypeInfo: LONGINT): SYSTEM.ADDRESS;
	VAR
		result: SYSTEM.ADDRESS;
		leftDispatchType, rightDispatchType: LONGINT;
		leftLevel, rightLevel: SHORTINT;
		key: Key;
		found: BOOLEAN;
		hashValue: LONGINT;
	BEGIN (* {EXCLUSIVE} *)
		(* determine the dispatch types and operator kind *)
		IF leftPointer = NonPointer THEN
			(* no pointer type: use fingerprint, which is stored in type-info *)
			ASSERT(leftTypeInfo # NoType);
			leftDispatchType := leftTypeInfo;
			key.kind := {};
		ELSIF leftPointer = NilValue THEN
			(* pointer is NIL: use the static type, whose typetag is stored in type-info *)
			leftDispatchType := leftTypeInfo; (* type-info is the typetag of the static type *)
			key.kind := {LhsIsPointer}
		ELSE
			(* type info irrelevant; determine runtime type of pointer *)
			SYSTEM.GET(leftPointer - AddressSize, leftDispatchType);
			key.kind := {LhsIsPointer}
		END;
		IF rightPointer = NonPointer THEN
			(* no pointer type: use fingerprint, which is stored in type-info (for unary operators type-info may also be set to 'NoType') *)
			rightDispatchType := rightTypeInfo
		ELSIF rightPointer = NilValue THEN
			(* pointer is NIL: use the static type, whose typetag is stored in type-info *)
			rightDispatchType := rightTypeInfo;
			key.kind := key.kind + {RhsIsPointer}
		ELSE
			(* normal pointer: determine runtime type (ignore type-info) *)
			SYSTEM.GET(rightPointer - AddressSize, rightDispatchType);
			key.kind := key.kind + {RhsIsPointer}
		END;
		
		key.identifier := identifier;
		key.leftType := leftDispatchType;
		key.rightType := rightDispatchType;
		
		IF hashTable.Has(key) THEN
			(* entry exists in the table *)
			
			Debugging.String(">>> direct match!"); Debugging.Ln; (* TENTATIVE *)
			
			result := hashTable.Get(key)
		ELSE
			Debugging.String(">>> do polymorphic search"); Debugging.Ln; (* TENTATIVE *)

		
			(* no entry exists: do polymorphic search *)
			found := FALSE;
			IF key.kind = {LhsIsPointer, RhsIsPointer} THEN
				(* 2D-polymorphic search *)
				leftLevel := LevelOfType(leftDispatchType);
				WHILE ~found & (leftLevel >= 0) DO
					key.leftType := TypeOfLevel(leftDispatchType, leftLevel);
					rightLevel := LevelOfType(rightDispatchType);
					WHILE ~found & (rightLevel >= 0) DO
						key.rightType := TypeOfLevel(rightDispatchType, rightLevel);
						found := hashTable.Has(key);
						DEC(rightLevel)
					END;
					DEC(leftLevel)
				END
			ELSIF key.kind = {LhsIsPointer} THEN
				(* 1D-polymorphic search *)
				leftLevel := LevelOfType(leftDispatchType);
				WHILE ~found & (leftLevel >= 0) DO
					key.leftType := TypeOfLevel(leftDispatchType, leftLevel);
					key.rightType := rightDispatchType;
					found := hashTable.Has(key);
					DEC(leftLevel)
				END
			ELSIF key.kind = {RhsIsPointer} THEN
				(* 1D-polymorphic search *)
				rightLevel := LevelOfType(rightDispatchType);
				WHILE ~found & (rightLevel >= 0) DO
					key.leftType := leftDispatchType;
					key.rightType := TypeOfLevel(rightDispatchType, rightLevel);
					found := hashTable.Has(key);
					DEC(rightLevel)
				END
			ELSE
				HALT(100)
			END;
			ASSERT(found);
			ASSERT(hashTable.Has(key));
			result := hashTable.Get(key);
			
			(* register the operator for the given types, such that it does not have to be searched again *)
			RegisterOperator(key.identifier, key.kind, leftDispatchType, rightDispatchType, result)
		END;
		RETURN result
	END SelectOperator;

BEGIN
	NEW(hashTable, InitialHashTableSize);

END FoxOperatorRuntime.

Compiler.Compile FoxOperatorRuntime -b=AMD ~

SystemTools.Free FoxOperatorRuntime ~

FoxOperatorRuntime.DumpHashTable ~

