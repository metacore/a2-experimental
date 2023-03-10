MODULE StatisticsBase; (** AUTHOR "Patrick Hunziker"; PURPOSE "tools for statistics"; *)

IMPORT MatrixBase, MathL, MatrixUtilities;

TYPE
	Matrix*=MatrixBase.Matrix;
	Vector*=MatrixBase.Vector;
	Datatype*=MatrixBase.Datatype;
	Array*=ARRAY[?] OF Datatype;

VAR arrayFunctionsPool:=NEW ArrayFunctionsPool:ArrayFunctionsPool;

TYPE ArrayFunctionsPool=OBJECT
	VAR pool,f:ArrayFunction;
	PROCEDURE Get():ArrayFunction;
	BEGIN {EXCLUSIVE} (*can we circumvent locking here ?*)
		IF pool#NIL THEN 
			f:=pool; pool:=f.next; f.next:=NIL;
		ELSE 
			NEW(f);
		END;
		RETURN f
	END Get;
	
	PROCEDURE Put(f:ArrayFunction);
	BEGIN {EXCLUSIVE}
		IF f#NIL THEN f.Init; f.next:=pool; pool:=f END;
	END Put;
END ArrayFunctionsPool;

TYPE ArrayFunction= OBJECT 
	VAR min,max,sum,mean, msq,scale,ssq:REAL;
		cnt:SIZE;
		next:ArrayFunction;(*linked list*)
	PROCEDURE &Init;
	BEGIN
		sum:=0;
		min:=MAX(Datatype);
		max:=MIN(Datatype);
		mean:=0;
		msq:=0; ssq:=0;
		cnt:=0;
		scale:=1;
	END Init;
	
	PROCEDURE AddAbs(x:REAL)(*:REAL*);
	BEGIN
		sum:=sum+ABS(x);
		(*RETURN x*)
	END AddAbs;

	PROCEDURE MaxAbs(x:REAL)(*:REAL*);
	BEGIN
		max:=MAX(max,ABS(x));
		(*RETURN x*)
	END MaxAbs;

	PROCEDURE MinAbs(x:REAL)(*:REAL*);
	BEGIN
		min:=MIN(min,ABS(x));
		(*RETURN x*)
	END MinAbs;
	
	PROCEDURE Variance(x:REAL);(*!precondition: assign 'mean'*)
	BEGIN
		ssq:=ssq+(x-mean)*(x-mean);
		INC(cnt)
	END Variance;(*!postcondition: divide 'ssq' by 'cnt'*)

	PROCEDURE SumSquare(x:REAL);
	BEGIN
		ssq:=ssq+ x*x;
	END SumSquare;
	
	END ArrayFunction;

PROCEDURE HasSize*(CONST a: Array; CONST size: ARRAY [*] OF SIZE):BOOLEAN;
VAR i:SIZE;
BEGIN
	IF (DIM(a)#LEN(size,0)) THEN RETURN FALSE
	ELSE
		FOR i:=0 TO DIM(a)-1 DO
			IF LEN(a,i)#size[i] THEN RETURN FALSE END;
		END;
		RETURN TRUE;
	END;
END HasSize;

PROCEDURE MakeSize*(VAR a:Array; CONST len:ARRAY [*] OF SIZE);
	BEGIN
		IF ~HasSize(a,len) THEN	NEW(a,len) (*ELSE a:=0*) END;(*? fill with zeros or not ?*)
	END MakeSize;
	
PROCEDURE SameSize*(CONST a,b: Array):BOOLEAN;
VAR i:SIZE;
BEGIN
	IF (DIM(a)#DIM(b)) OR (DIM(a)=0) THEN RETURN FALSE
	ELSE
		FOR i:=0 TO DIM(a)-1 DO
			IF LEN(a,i)#LEN(b,i) THEN RETURN FALSE END;
		END;
		RETURN TRUE;
	END;
END SameSize;



PROCEDURE Count*(CONST a: Array):SIZE;
VAR i:SIZE; res:SIZE;
BEGIN
	IF DIM(a)=0 THEN res:=0
	ELSE
		res:=1;
		FOR i:=0 TO DIM(a)-1 DO
			res:=res*LEN(a,i);
		END;
	END;
	RETURN res
END Count;

PROCEDURE Prod*(CONST v: Vector):Datatype;
VAR i:SIZE; x:Datatype;
BEGIN
	x:=v[0];
	FOR i:=1 TO LEN(v,0)-1 DO x:=x*v[i] END;
	RETURN x;
END Prod;

PROCEDURE ProdS*(CONST v: ARRAY [*] OF SIZE):Datatype;
VAR i:SIZE; x:SIZE;
BEGIN
	x:=v[0];
	FOR i:=1 TO LEN(v,0)-1 DO x:=x*v[i] END;
	RETURN Datatype(x);
END ProdS;

PROCEDURE MinAbs*(CONST a:ARRAY[?] OF Datatype):Datatype; (*is VAR instead of CONST because of performance limitation of compiler*)
VAR f:ArrayFunction; res:Datatype;
BEGIN
	f:=arrayFunctionsPool.Get();(*?what is the impact of locking on performance ?*)
	f.Init; 
	f.MinAbs(a);
	res:=f.min;
	arrayFunctionsPool.Put(f);(*?what is the impact of locking on performance ?*)
	RETURN res
END MinAbs;

PROCEDURE MaxAbs*(CONST a:ARRAY[?] OF Datatype):Datatype; (*is VAR instead of CONST because of performance limitation of compiler*)
VAR f:ArrayFunction; res:Datatype;
BEGIN
	f:=arrayFunctionsPool.Get();
	f.Init; 
	f.MaxAbs(a);
	res:=f.max;
	arrayFunctionsPool.Put(f);
	RETURN res
END MaxAbs;

PROCEDURE SumAbs*(CONST a:ARRAY[?] OF Datatype):Datatype; (*is VAR instead of CONST because of performance limitation of compiler*)
VAR f:ArrayFunction; res:Datatype;
BEGIN
	f:=arrayFunctionsPool.Get();
	f.Init; 
	f.AddAbs(a);
	res:=f.sum;
	arrayFunctionsPool.Put(f);
	RETURN res
END SumAbs;

PROCEDURE Mean*(CONST X: Array): Datatype;
VAR cnt: SIZE;
BEGIN
	cnt:=Count(X);
	IF cnt=0 THEN RETURN 0 (*? or NaN  ?*)
	ELSE RETURN SUM(X)/cnt
	END;
END Mean;

(*PROCEDURE MeanSquare*(CONST X: Array): Datatype;
VAR cnt: SIZE;
	f:ArrayFunction;
	res:Datatype;
BEGIN
	IF DIM(X)=0 THEN RETURN 0 END;
	cnt:=Count(X);
	IF cnt=0 THEN RETURN 0 
	ELSE (*in this version, division is applied at each element squaring, to avoid overflow of the sum. More costly, more robust. But no allocations.*)
		f:=arrayFunctionsPool.Get();
		f.SumSquare(X);
		res:=f.ssq/cnt;
		arrayFunctionsPool.Put(f);
		RETURN res
	END;
END MeanSquare;
*)

 
PROCEDURE MeanSquare*(CONST X: Array): Datatype;
VAR cnt: SIZE;
BEGIN
	cnt:=Count(X);
	IF cnt=0 THEN RETURN 0 (*? or NaN  ?*)
	ELSE RETURN X+*X/cnt
	END;
END MeanSquare;


PROCEDURE RMS*(CONST X: Array): Datatype; (*root mean square*)
BEGIN
	RETURN MathL.sqrt(MeanSquare(X));
END RMS;

(*PROCEDURE RMS*(CONST X: Array): Datatype; (*root mean square*)
BEGIN
	IF DIM(X)=0 THEN RETURN 0 (*!TBD: apply to other structures ? or TRAP ?*)
	ELSE RETURN MathL.sqrt(X+*X / Count(X))
	(*ELSE RETURN MathL.sqrt(X+*X / ProdS(LEN(X)))*)
	END;
END RMS;*)

PROCEDURE KSmallest*( VAR a: Vector; (* n,*) k: SIZE ): Datatype;
(** caution: modifies a , Algorithm by N.Wirth / Hoare, cf. N. Wirth: Algorithms & Datastructures. *)
VAR i, j, l, m, n: SIZE;  x: Datatype;

	PROCEDURE swap( VAR x, y: Datatype );
	VAR z: FLOAT64;
	BEGIN
		z := x;  x := y;  y := z
	END swap;

BEGIN
	n:=LEN(a,0);
	l := 0;  m := n - 1;
	WHILE (l < m) DO
		x := a[k];  i := l;  j := m;
		REPEAT
			WHILE (a[i] < x) DO INC( i ) END;
			WHILE (x < a[j]) DO DEC( j ) END;
			IF i <= j THEN swap( a[i], a[j] );  INC( i );  DEC( j ) END
		UNTIL i > j;
		IF j < k THEN l := i END;
		IF k < i THEN m := j END
	END;
	RETURN a[k]
END KSmallest;

PROCEDURE QSort*(VAR X : Vector);
	PROCEDURE Sort(l, r : SIZE);
	VAR
		i, j : SIZE;
		u, v : Datatype;
	BEGIN
		i := l;
		j := r;
		u := X[(l+r) DIV 2];
		REPEAT
			WHILE  (X[i] < u) DO INC(i) END;
			WHILE (u < X[j]) DO DEC(j) END;
			IF i <= j THEN
				v := X[i]; X[i] := X[j]; X[j] := v;
				INC(i); DEC(j);
			 END;
		UNTIL i > j;
		IF l < j THEN Sort(l, j) END;
		IF i < r THEN Sort(i, r) END;
	END Sort;
 BEGIN
	Sort(0, LEN(X,0)-1);
 END QSort;

 PROCEDURE DestructiveMedian*(VAR v1:Vector):Datatype;
 VAR len:SIZE;
 BEGIN
 	len:=LEN(v1,0);
	IF ODD( len ) THEN RETURN KSmallest( v1, (*len,*) len DIV 2 )
	ELSE RETURN (KSmallest( v1, (*len,*) len DIV 2 - 1 ) + KSmallest( v1, (*len,*) len DIV 2 )) / 2
	END
 END DestructiveMedian;

 PROCEDURE Median*(CONST v:Vector):Datatype;
 VAR v1:Vector;
 BEGIN
 	v1:=v;(* leave original data intact, at the price of memory allocation*)
 	RETURN DestructiveMedian(v1)
 END Median;

 (** variance of dataset *)
(* PROCEDURE Variance*(CONST v:Array):Datatype;
 VAR diff:Array;
 BEGIN
 	 diff:=v-Mean(v);
 	 RETURN MeanSquare(diff)
 	(* RETURN (diff+*diff) / Count(v) *)
 END Variance;*)

 (** variance of dataset *)
 PROCEDURE Variance*(CONST a:ARRAY[?] OF Datatype):Datatype;
 VAR f:ArrayFunction; res:Datatype;
 BEGIN
 	f:=arrayFunctionsPool.Get();(*?what is the impact of locking on performance ?*)
 	f.Init; 
 	f.mean:=Mean(a);
 	f.Variance(a);
 	res:=f.ssq/f.cnt;
 	arrayFunctionsPool.Put(f);(*?what is the impact of locking on performance ?*)
 	RETURN res
 END Variance;

 (** of full data *)
 PROCEDURE StandardDeviation*(CONST v:Array): Datatype;
 BEGIN
 	RETURN MathL.sqrt(Variance(v))
 END StandardDeviation;


	(** variance estimated from subset of data, divisor is (N-1)*)
 PROCEDURE EstimatedVariance*(CONST v:Array):Datatype;
 VAR f:ArrayFunction; res:Datatype;
 BEGIN
 	f:=arrayFunctionsPool.Get();
 	f.Init; 
 	f.mean:=Mean(v);
 	f.Variance(v);
 	res:=f.ssq/(f.cnt-1);
 	arrayFunctionsPool.Put(f);
 	RETURN res
 END EstimatedVariance;

 (** subset of data , divisor is (N-1)*)
 PROCEDURE EstimatedStandardDeviation*(CONST v:Array): Datatype;
 BEGIN
 	RETURN MathL.sqrt(EstimatedVariance(v))
 END EstimatedStandardDeviation;

 PROCEDURE Skewness*(CONST X : Array) : Datatype;
	VAR
		sigma : Datatype;
		x1: Array;
	BEGIN
		sigma:=StandardDeviation(X);
		x1:=X-Mean(X);
		RETURN  ((x1 .* x1) +* x1) / (sigma*sigma*sigma)/ Count(X)
	END Skewness;

PROCEDURE Kurtosis*(CONST X : Array) : Datatype;
	VAR
		variance: Datatype;
		x1,x2:Array;
	BEGIN
		variance:=Variance(X);
		x1:=X-Mean(X);
		x2:=x1.*x1;
		RETURN (x2 +* x2) / (variance*variance) / Count(X) - 3;
	END Kurtosis;
	

(* possi ble solution for sum abs:
MODULE Test; 

IMPORT Commands;

TYPE Summer*= OBJECT
	VAR sum:REAL;
	PROCEDURE &Init*;
	BEGIN
		sum:=0;
	END Init;
	
	PROCEDURE AddAbs(x:REAL):REAL;
	BEGIN
		sum:=sum+ABS(x);
		RETURN x
	END AddAbs;
	
	END Summer;
	
PROCEDURE Do*(c:Commands.Context);
	VAR a: ARRAY [*] OF REAL;
		summer:Summer;
	BEGIN
		a:=[-1,-1,-1,1,1,1];
		NEW(summer);
		a:=summer.AddAbs(a);
		c.out.FloatFix(summer.sum,10,4,0); c.out.Ln; c.out.Update;
		
	END Do;
	


END Test.

Test.Do ~

*)



PROCEDURE Normalize*(CONST a: Array):Array;
VAR N:SIZE; sd: Datatype;
BEGIN
	N:=Count(a);
	RESULT:=a-SUM(a)/N;
	sd:=MathL.sqrt( RESULT+*RESULT / N);
	IF sd=0 THEN RETURN RESULT (* avoid NaN result in this case*)
	ELSE RETURN 1/sd * RESULT
	END;
END Normalize;

PROCEDURE NormalizeColumns*(VAR A:Matrix); (*normalizing to mean=0 and SD=1*)
VAR onesR, meanVector,sdVector: Vector; meanMatrix, sdMatrix:Matrix;
BEGIN
	NEW(onesR, LEN(A,0));
	onesR:=1;
	meanVector := (onesR * A)/LEN(A,0);
	meanMatrix := onesR ** meanVector;
	A:=A-meanMatrix;
	sdVector := MatrixUtilities.ApplyUnaryVec(onesR * (A.*A), MathL.sqrt) / MathL.sqrt(LEN(A,0));
	sdMatrix:= onesR ** sdVector;
	A:= A ./ sdMatrix;
END NormalizeColumns;

(* subtract column mean from each column *)
PROCEDURE ZeroMeanColumns*(VAR A:Matrix);
	VAR onesR, meanVector: Vector;
BEGIN
	NEW(onesR, LEN(A,0));
	onesR:=1;
	meanVector := (onesR * A)/LEN(A,0);
	A:=A - onesR ** meanVector;
END ZeroMeanColumns;

(*! to do: move the following proc's  to higher level modules - may not be basic statistics  *)
(** SoftMax  of a data vector = Normalized exponential; SUM=1.0
 y[i] = softmax(x[i]) = exp(x[i])/sum(exp(x)) *)
PROCEDURE SoftMax*(VAR x: Array):Array;
	BEGIN
		RESULT :=ALL(x, MathL.exp);
		RESULT:=1/SUM(RESULT) * RESULT;
		RETURN RESULT
END SoftMax;

PROCEDURE Logistic*(X : Datatype) : Datatype;  (* logistic function as nonlinear element for unit response *)
	BEGIN
		IF X >= 18.3684002848 (*expNegligibleL*) THEN RETURN 1
		ELSIF (-X) > 18.3684002848 (*expNegligibleL*) THEN RETURN 0
		ELSE RETURN 1 / (1 + MathL.exp( -X ));
		END;
	END Logistic;

(**
Normalize input such that input mean(x)=0, input SD(x)=1, then bring to [0..1] using SoftMax sigmoid transform
 y[i] = softmax(x[i]) = exp(x[i])/sum(exp(x)) *)
PROCEDURE SoftMaxNormalize*(CONST x: Array):Array;
	BEGIN
		RESULT:=Normalize(x);
		RESULT :=ALL(RESULT, Logistic);
		RETURN RESULT
END SoftMaxNormalize;
(*
PROCEDURE Test*;
CONST a=[1,2,3,4]; b=[1,2,2,1]; c=[1,2,3,2]; d=[1,1,2,3,1]
BEGIN
	MatrixUtilities.OutVector([Skewness(a)]);
	MatrixUtilities.OutVector([Skewness(b)]);
	MatrixUtilities.OutVector([Skewness(c)]);
	MatrixUtilities.OutVector([Skewness(d)]);
	MatrixUtilities.OutVector([Kurtosis(a)]);
	MatrixUtilities.OutVector([Kurtosis(b)]);
	MatrixUtilities.OutVector([Kurtosis(c)]);
	MatrixUtilities.OutVector([Kurtosis(d)]);
END Test;
*)

(*
PROCEDURE TestNormalizeColumns*;
VAR A:Matrix;
BEGIN
	A:=[[1,2,3,4],[2,3,4,8],[3,4,5,12],[4,5,6,16]];
	NormalizeColumns(A);
	MatrixUtilities.OutMatrix(A);
END TestNormalizeColumns;
*)

PROCEDURE TestSort*;
VAR v:Vector; zero: Datatype;
BEGIN
	v:=[0, 1, -1/zero, 1/zero, 4,3,2,3,4,5];
	QSort(v);
	MatrixUtilities.OutVector(v);
END TestSort;

PROCEDURE TestSumAbs*;
VAR v:Vector; sumAbs,minAbs,maxAbs:Datatype; count, i:SIZE;
BEGIN
	NEW(v,10000);
	FOR i:=0 TO LEN(v,0)-1 DO IF ODD(i) THEN v[i]:=0.5 ELSE v[i]:=-1.5 END END;
	sumAbs:=SumAbs(v);
	minAbs:=MinAbs(v);
	maxAbs:=MaxAbs(v);
	count:=Count(v);
	TRACE(sumAbs,minAbs,maxAbs);
	HALT(200)
END TestSumAbs;


PROCEDURE TestMedian*;
VAR v:Vector; zero: Datatype;
BEGIN
	v:=[0, 1, -1/zero, 1/zero, 4,3,2,3,4,5];
	MatrixUtilities.OutVector(v);
	MatrixUtilities.OutVector([Median(v)])
END TestMedian;

PROCEDURE TestSoftMax*;
VAR v,v1:Vector;
BEGIN
	v:=[0, 1, 2, 3, 4,3,2,3,4,5];
	v1:=Normalize(v);
	MatrixUtilities.OutVector(v1);
	MatrixUtilities.OutVector([StandardDeviation(v1)]);
	MatrixUtilities.OutVector([Mean(v1)]);
	v1:=SoftMaxNormalize(v);
	MatrixUtilities.OutVector(v1);
	MatrixUtilities.OutVector([Median(v1)]);
	MatrixUtilities.OutVector([Mean(v1)]);
	MatrixUtilities.OutVector([StandardDeviation(v1)])
END TestSoftMax;

PROCEDURE {TEST} Test*;(*! implement more tests ! *)
CONST TestTolerance=0.000000001; 
VAR v:Vector;x:Datatype;
BEGIN
	ASSERT(Count([[[1,2,3],[4,5,6]],[[1,2,3],[4,5,6]]])=12, 200);
	ASSERT(Mean([1,2,3,4,5,6])=3.5, 201);
	ASSERT(Median([4,3,2,1,5,6,7])=4, 202);
	x:=MeanSquare([1,2,3,4,5]) - [1,2,3,4,5]+*[1,2,3,4,5]/5; ASSERT(ABS(x)<TestTolerance, 203);
	ASSERT(Prod([1,2,3,4,5])=120 ,204);
	ASSERT(Variance([1,2,3,4,5])= ([1,2,3,4,5]-3)+*([1,2,3,4,5]-3)/5, 205);
	ASSERT(EstimatedVariance([1,2,3,4,5])= ([1,2,3,4,5]-3)+*([1,2,3,4,5]-3)/4, 206);
	ASSERT(ABS(StandardDeviation(Normalize([1,2,3,4,5]))-1)<TestTolerance, 207);
	ASSERT(SumAbs([-1,1,-3,2])=7, 208);
	ASSERT(MinAbs([-1,1,-3,2])=1, 209);
	ASSERT(MaxAbs([-1,1,-3,2])=3, 210); 
	
	v:=[5,2,1,4,3]; QSort(v); ASSERT(v=[1,2,3,4,5], 207);
END Test;


END StatisticsBase.

StatisticsBase.TestSort ~
StatisticsBase.TestSumAbs ~
StatisticsBase.TestMedian ~
StatisticsBase.TestSoftMax ~
StatisticsBase.Test ~

System.FreeDownTo StatisticsBase ~
