MODULE ArrayRotations;   (**  AUTHOR "Patrick Hunziker"; PURPOSE "rotation decompositions in 2D and 3D";  **)
(** example of rotation of a point or vector by a matrix: [x1,y1,z1] := R * [x0,y0,z0] ;
	example of concatenated rotatations: v1:= R2*R1*v0 ; *)
(** CAVE: order of rotations ! *)
(*mathematics of rotations; see http://mathworld.wolfram.com/EulerAngles.html and wikipedia *)
(*conventions: axis designators: small caps = do not rotate with object transformation; capitals: axes move with object*)
(*rotation around x=phi; around y=theta; around z=psi*)
(*for properties of rotation matrix, real, orthogonal, determinant +1; i.e. orthonormal; see special orthogonal group SO(3);
	note that QR decomposition delivers an orthonormal matrix from M; 
	the polar decomposiition ()Fan&Hoffman 1955; Higham 1989 produces a Q 'closest' to M *)

IMPORT MathL, MatrixUtilities, Reals, KernelLog, Commands, Streams;  

CONST 
	Sxyzx* = 1;  Sxzyx* = 2;  
	Syxzy* = 3;  Syzxy* = 4;  
	Szxyz* = 5;  Szyxz* = 6;  
	GimbalLock* = -1;  

TYPE 
	Datatype = FLOAT64;  Vector = ARRAY [ * ] OF Datatype;  
	Matrix = ARRAY [ * , * ] OF Datatype;  
	
	(*
PROCEDURE MatrixToEuler3D(Rotation:Matrix):Vector;
END MatrixToEuler3D;

(* zxz convention == 313 convention, "x-convention": full rotation described by RotZ(phi),RotX(theta),RotZ(psi) (sic!) *)
PROCEDURE EulerzxzToMatrix(Euler:Vector):Matrix; (*x-convention zxz*)
BEGIN
	sphi:=sin(phi); cphi:=cos(phi);
	stheta:=sin(theta); ctheta:=cos(theta);
	spsi:=sin(psi); cpsi:=cos(psi);
	RETURN [[cpsi*cphi-ctheta*sphi*spsi,	cpsi*sphi+ctheta*cphi*sphi,	spsi*stheta],
			[-spsi*cphi- ctheta*sphi*cpsi,	-spsi*sphi+ctheta*cphi*cpsi,	cpsi*stheta], 
			[stheta*sphi,					-stheta*cphi,				ctheta]];
	END EulerzxzToMatrix;

PROCEDURE MatrixToEulerzxz(Rotation:Matrix):Vector; (*x-convention zxz*)
BEGIN
	phi:=atan2(R[2,0],R[2,1]);
	theta:=acos(R[2,2]);
	psi:=-atan2(R[0,2],R[1,2]);
	RETURN [phi,theta,psi];
END MatrixToEulerzxz;

(*untested*)
PROCEDURE EulerXYZToMatrix(Euler:Vector):Matrix; (*"pitch-roll-yaw": full rotation described by pitch(theta),roll(psi),yaw(phi) around the moving body axes (sic!) *)
BEGIN
	sphi:=sin(phi); cphi:=cos(phi);
	stheta:=sin(theta); ctheta:=cos(theta);
	spsi:=sin(psi); cpsi:=cos(psi);
	RETURN [[ctheta*cphi,				ctheta*sphi,					-stheta],
			[spsi*stheta*cphi-cpsi*sphi,	spsi*stheta*sphi+cpsi*cphi,	ctheta*spsi], 
			[cpsi*stheta*cphi+spsi*sphi,	cpsi*stheta*sphi-spsi*cphi,	ctheta*cpsi]];
END EulerXYZToMatrix;
*)
	
	PROCEDURE sin( x: Datatype ): Datatype;  
	BEGIN 
		RETURN MathL.sin( x )
	END sin;  

	PROCEDURE cos( x: Datatype ): Datatype;  
	BEGIN 
		RETURN MathL.cos( x )
	END cos;  

	PROCEDURE EulerxyzToMatrix*( phi, theta, alpha: Datatype ): Matrix;   (* composes rotation matrix Rzyx from 1)rotationX(phi), 2)rotationY(theta), 3)rotationZ(alpha); coordinate system is fix*)
	VAR Rxyz, Rzyx: Matrix;  
	BEGIN 
		
		(*Rzyx implies cosecutive rotation along X,Y,Z in this order, corresponding to the rotation matrix Rz*Ry*Rx *)
		NEW( Rzyx, 3, 3 );
		Rzyx[0, 0] := (cos(alpha)*cos(theta));  
		Rzyx[0, 1] := ((sin(alpha)*cos(phi))+(cos(alpha)*sin(theta)*(-sin(phi))));  
		Rzyx[0, 2] := ((sin(alpha)*sin(phi))+(cos(alpha)*sin(theta)*cos(phi)));  
		Rzyx[1, 0] := ((-sin(alpha))*cos(theta));  
		Rzyx[1, 1] := ((cos(alpha)*cos(phi))+((-sin(alpha))*sin(theta)*(-sin(phi))));  
		Rzyx[1, 2] := ((cos(alpha)*sin(phi))+((-sin(alpha))*sin(theta)*cos(phi)));  
		Rzyx[2, 0] := (-sin(theta));  
		Rzyx[2, 1] := (cos(theta)*(-sin(phi)));  
		Rzyx[2, 2] := (cos(theta)*cos(phi)); 

		RETURN Rzyx
		
		(*		NEW( Rxyz, 3, 3 );   (*i.e. Rx*Ry*Rz * v ; i.e. sequential rotations of v by Rz, then by Ry, then by Rx *) (* to do: simplify by computing sin,cos only once*)
		Rxyz[0, 0] := (cos( phi ) * cos( theta ));  
		Rxyz[0, 1] := ((sin( phi ) * cos( alpha )) + (cos( phi ) * sin( theta ) * (-sin( alpha ))));  
		Rxyz[0, 2] := ((sin( phi ) * sin( alpha )) + (cos( phi ) * sin( theta ) * cos( alpha )));  
		Rxyz[1, 0] := ((-sin( phi )) * cos( theta ));  
		Rxyz[1, 1] := ((cos( phi ) * cos( alpha )) + ((-sin( phi )) * sin( theta ) * (-sin( alpha ))));  
		Rxyz[1, 2] := ((cos( phi ) * sin( alpha )) + ((-sin( phi )) * sin( theta ) * cos( alpha )));  
		Rxyz[2, 0] := (-sin( theta ));  
		Rxyz[2, 1] := (cos( theta ) * (-sin( alpha )));  
		Rxyz[2, 2] := (cos( theta ) * cos( alpha ));  
*)

		(*
	sphi:=sin(phi); cphi:=cos(phi);
	stheta:=sin(theta); ctheta:=cos(theta);
	salpha:=sin(alpha); calpha:=cos(alpha);
	Rx:=[[cphi,		sphi,		0], 
			[-sphi,	 cphi,		0], 
			[0,			0,			1]];
	Ry:=[[ctheta,		0,	stheta], 
			[0,	1,	0], 
			[-stheta,	0,	ctheta]] ;
	Rz:=[[1,	0,	0],					
			[0,	calpha,		salpha],
			[0,	-salpha,		calpha]];
					
	RETURN [[cphi,		sphi,		0], (*last rotation - note that the entity to be rotated follows on the right of the rotation matrix ! *)
					[-sphi,	 cphi,		0], 
					[0,			0,			1]
					*
					[ctheta,		0,	stheta], (*second rotation*)
					[0,	1,	0], 
					[-stheta,	0,	ctheta]] 
					*
					[1,	0,	0],					(*first rotation*)
					[0,	calpha,		salpha],
					[0,	-salpha,		calpha]]
		*)
	END EulerxyzToMatrix;  
(*
PROCEDURE AxisAngleToMatrix(x,y,z,theta:Datatype); (*Euler rotation defined by unit vector [x,y,z] and angle theta;*)
VAR c,s,C,xs,ys,zs,xC,yC,zC,xyC,yzC,zxC:Datatype;
BEGIN
	c := cos(theta); s := sin(theta); C := 1-c
	xs := x*s;   ys := y*s;   zs := z*s;
	xC := x*C;   yC := y*C;   zC := z*C;
	xyC := x*yC; yzC := y*zC; zxC := z*xC;
	RETURN [[ x*xC+c,   xyC-zs,   zxC+ys ],
					[ xyC+zs,   y*yC+c,   yzC-xs ],
					[ zxC-ys,   yzC+xs,   z*zC+c ]]
END AxisAngleToMatrix;

PROCEDURE IsRotation(CONST Rotation:Matrix):BOOLEAN;
VAR QR:MatrixStandardSolvers.QR;
BEGIN
	IF MatrixNorms.Det(Rotation) # 1 THEN RETURN FALSE (*to do: allow for roundoff error*)
	ELSIF 
	NEW(QR,Rotation); 
	IF QR.R is UnitMatrix (i.e., Q equals Rotation which is orthonormal ) THEN RETURN TRUE
	ELSE RETURN FALSE
	END;
END IsRotation;
*)
	PROCEDURE sqr( x: Datatype ): Datatype;  
	BEGIN 
		RETURN x * x
	END sqr;  

	PROCEDURE CheckFactorization( CONST param: Vector;  variant: SIGNED32 );  (*checks if factorization of 3D rotation into four 1D shears gives correct results *)
	VAR Sx, Sy, Sz, Sx2, Sy2, Sz2: Matrix;  a, b, c, d, e, f, g, h: Datatype;  
	BEGIN 
		a := param[0];  b := param[1];  c := param[2];  d := param[3];  e := param[4];  f := param[5];  g := param[6];  h := param[7];  
		Sx := [[1, 0, 0], [0, 1, 0], [0, 0, 1]];  Sx[1, 0] := a;  Sx[2, 0] := b;  
		Sy := [[1, 0, 0], [0, 1, 0], [0, 0, 1]];  Sy[0, 1] := c;  Sy[2, 1] := d;  
		Sz := [[1, 0, 0], [0, 1, 0], [0, 0, 1]];  Sz[0, 2] := e;  Sz[1, 2] := f;  
		Sx2 := [[1, 0, 0], [0, 1, 0], [0, 0, 1]];  Sx2[1, 0] := g;  Sx2[2, 0] := h;  
		Sy2 := [[1, 0, 0], [0, 1, 0], [0, 0, 1]];  Sy2[0, 1] := g;  Sy2[2, 1] := h;  
		Sz2 := [[1, 0, 0], [0, 1, 0], [0, 0, 1]];  Sz2[0, 2] := g;  Sz2[1, 2] := h;  
		CASE variant OF 
		1:     MatrixUtilities.OutMatrix( Sx * Sy * Sz * Sx2 );   (* operations from right to left; i.e, shear operation Sx2 is performed first, Sx is performed last; data term is to the right of transform matrices ! *)
		| 2:   MatrixUtilities.OutMatrix( Sx * Sz * Sy * Sx2 );  
		| 3:   MatrixUtilities.OutMatrix( Sy * Sx * Sz * Sy2 );  
		| 4:   MatrixUtilities.OutMatrix( Sy * Sz * Sx * Sy2 );  
		| 5:   MatrixUtilities.OutMatrix( Sz * Sx * Sy * Sz2 );  
		| 6:   MatrixUtilities.OutMatrix( Sz * Sy * Sx * Sz2 );  
		END;  
	END CheckFactorization;  


(** decomposes full 3D rotation from rotation matrix R into one of the possible sequences of 4 consecutive shear transforms; 
	there are at least 6 variants; and the one with the lowest sum of squares for parameters a,b,c,d,e,f,g,h is chosen. Note that there are still invalid cases near 0,90,180 degree rotation. *)
	PROCEDURE Rotation4ShearDecomposition*( CONST Rotation: Matrix;  VAR bestparam: Vector ): SIGNED32;  
	VAR a, b, c, d, e, f, g, h, r11, r12, r13, r21, r22, r23, r31, r32, r33: Datatype;  sos, bestsos: Datatype;  best: SIGNED32;  param: Vector;  
	BEGIN 
		r11 := Rotation[0, 0];  r12 := Rotation[0, 1];  r13 := Rotation[0, 2];  
		r21 := Rotation[1, 0];  r22 := Rotation[1, 1];  r23 := Rotation[1, 2];  
		r31 := Rotation[2, 0];  r32 := Rotation[2, 1];  r33 := Rotation[2, 2];  
		NEW( param, 8 );  bestparam:=param; bestsos:=5000;
		best:=GimbalLock;
		(* xyzx: *)
		param[0] := (r22 - 1)*(r21*r33 - r23*r31) / (r21*r32*r13 + r33*r22*r11 - r32*r23*r11 - r13*r31*r22 - 1);  
		param[1] := 	-(r21*r33 - r23*r31)*
			(sqr( r33 )*r22*r11 - r33*r32*r23*r11 - r33*r13*r31*r22 - r33 - r21*r32*r13 - r33*r22*r11 + r32*r23*r11 + r13*r31*r22 + 1 - sqr( r32 )*r23*r21*r13 - 
			  r32*r23*r33*r22*r11 + sqr( r32 )*sqr( r23 )*r11 + r32*r23 + r32*r13*r22*r21*r33 + r32*r13*r23*r31) / 
							(-r13*r22*r21*r33 + r23*r21*r32*r13 + r23*r33*r22*r11 - r32*sqr( r23 )*r11 - r23) / (r21*r32*r13 + r33*r22*r11 - r32*r23*r11 - r13*r31*r22 - 1);  
		param[2] := (r21*r32*r13 + r33*r22*r11 - r32*r23*r11 - r13*r31*r22 - 1) / (r21*r33 - r23*r31);  
		param[3] := 	(sqr( r33 )*r22*r11 - r33*r32*r23*r11 - r33*r13*r31*r22 - r33 - r21*r32*r13 - r33*r22*r11 + r32*r23*r11 + r13*r31*r22 + 1 + r32*r13*r23*r31) / 
			(-r13*r22*r21*r33 + r23*r21*r32*r13 + r23*r33*r22*r11 - r32*sqr( r23 )*r11 - r23);  
		param[4] := -(-r13*r22*r21*r33 + r23*r21*r32*r13 + r23*r33*r22*r11 - r32*sqr( r23 )*r11 - r23) / (r21*r33 - r23*r31);  
		param[5] := 	(r23*r21*r32*r13 + r23*r33*r22*r11 - r32*sqr( r23 )*r11 - r23 - r13*r22*r21*r33 + r13*r21*r33 - r13*r23*r31) / 
			(r21*r32*r13 + r33*r22*r11 - r32*r23*r11 - r13*r31*r22 - 1);  
		param[6] := 	(r21*r33 - r23*r31)*
			(-sqr( r13 )*sqr( r21 )*r32 - r13*r21*r33*r22*r11 + 2*r13*r21*r32*r23*r11 + sqr( r13 )*r21*r31*r22 + r13*r21 + r13*r22*r21*r33 - r13*r21*r33 + r13*r23*r31 + 
			  r23*sqr( r11 )*r33*r22 - sqr( r23 )*sqr( r11 )*r32 - r23*r11*r13*r31*r22 - r23*r11 - r23*r21*r32*r13 - r23*r33*r22*r11 + r32*sqr( r23 )*r11 + r23) / 
							(-r13*r22*r21*r33 + r23*r21*r32*r13 + r23*r33*r22*r11 - r32*sqr( r23 )*r11 - r23) / (r21*r32*r13 + r33*r22*r11 - r32*r23*r11 - r13*r31*r22 - 1);  
		param[7] := 	(-r21*r32*r23*r11 + r13*sqr( r21 )*r32 - r13*r21*r31*r22 - r21 + r21*r33 - r23*r31 + r23*r11*r31*r22) / 
			(-r13*r22*r21*r33 + r23*r21*r32*r13 + r23*r33*r22*r11 - r32*sqr( r23 )*r11 - r23);  
		sos := param +* param;  
		IF (~Reals.IsNaNL(sos)) & ( sos < bestsos) THEN best := 1;  bestsos := sos;  bestparam := param END;
		 MatrixUtilities.OutVector( param );  out.Int(1, 4);   out.FloatFix(sos,12,6,1); out.Ln; CheckFactorization( param, 1 );  out.Ln; 
		
		(* xzyx: *)
		
		param[0] := 	(r32*r21 - r31*r22)*
			(-r33*sqr( r22 )*r11 + r22*r12*r21*r33 + r22 + r32*r22*r23*r11 + r23*r12*r31 + r33*r22*r11 - r12*r21*r33 - 1 - r32*r23*r11 + r32*sqr( r23 )*r12*r31 + 
			  r32*r23*r33*r22*r11 - r32*r23 - sqr( r32 )*sqr( r23 )*r11 - r23*r12*r32*r21 - r12*r23*r33*r31*r22) / 
							(r32*r23*r12*r31 + r32*r33*r22*r11 - r32 - sqr( r32 )*r23*r11 - r12*r33*r31*r22) / (-r23*r12*r31 - r33*r22*r11 + r12*r21*r33 + 1 + r32*r23*r11);  
		param[1] := (-1 + r33)*(r32*r21 - r31*r22) / (-r23*r12*r31 - r33*r22*r11 + r12*r21*r33 + 1 + r32*r23*r11);  
		param[2] := (r32*r23*r12*r31 + r32*r33*r22*r11 - r32 - sqr( r32 )*r23*r11 - r12*r33*r31*r22) / (r32*r21 - r31*r22);  
		param[3] := 	-(r32*r23*r12*r31 + r32*r33*r22*r11 - r32 - sqr( r32 )*r23*r11 - r12*r32*r21 + r12*r31*r22 - r12*r33*r31*r22) / 
			(-r23*r12*r31 - r33*r22*r11 + r12*r21*r33 + 1 + r32*r23*r11);  
		param[4] := (-r23*r12*r31 - r33*r22*r11 + r12*r21*r33 + 1 + r32*r23*r11) / (r32*r21 - r31*r22);  
		param[5] := 	-(-r33*sqr( r22 )*r11 + r22*r12*r21*r33 + r22 + r32*r22*r23*r11 + r23*r12*r31 + r33*r22*r11 - r12*r21*r33 - 1 - r32*r23*r11 - r23*r12*r32*r21) / 
			(r32*r23*r12*r31 + r32*r33*r22*r11 - r32 - sqr( r32 )*r23*r11 - r12*r33*r31*r22);  
		param[6] := 	(-r31*r32*r23*r11 + sqr( r31 )*r12*r23 - r31*r12*r21*r33 - r31 - r32*r21 + r31*r22 + r32*r11*r21*r33) / 
			(r32*r23*r12*r31 + r32*r33*r22*r11 - r32 - sqr( r32 )*r23*r11 - r12*r33*r31*r22);  
		param[7] := 	-(r32*r21 - r31*r22)*
			(sqr( r31 )*sqr( r12 )*r23 + r31*r12*r33*r22*r11 - r31*sqr( r12 )*r21*r33 - r31*r12 - 2*r31*r12*r32*r23*r11 - r12*r32*r21 + r12*r31*r22 - r12*r33*r31*r22 - 
			  r32*sqr( r11 )*r33*r22 + r32*r11*r12*r21*r33 + r32*r11 + sqr( r32 )*sqr( r11 )*r23 + r32*r23*r12*r31 + r32*r33*r22*r11 - r32 - sqr( r32 )*r23*r11) / 
							(r32*r23*r12*r31 + r32*r33*r22*r11 - r32 - sqr( r32 )*r23*r11 - r12*r33*r31*r22) / (-r23*r12*r31 - r33*r22*r11 + r12*r21*r33 + 1 + r32*r23*r11);  
		sos := param +* param;  
		IF (~Reals.IsNaNL(sos)) & ( sos < bestsos) THEN best := 2;  bestsos := sos;  bestparam := param END;  
		MatrixUtilities.OutVector( param );  out.Int(2, 4);  out.FloatFix(sos,12,6,3); out.Ln; CheckFactorization( param, 2 );  out.Ln; 
		
		
		(* yxzy: *)
		param[0] := (r23*r12*r31 + r33*r22*r11 - r13*r31*r22 - 1 - r32*r23*r11) / (r12*r33 - r32*r13);  
		param[1] := 	-(sqr( r33 )*r22*r11 - r33*r13*r31*r22 - r33 - r33*r32*r23*r11 - r23*r12*r31 - r33*r22*r11 + r13*r31*r22 + 1 + r32*r23*r11 + r32*r13*r23*r31) / 
			(-r13*r23*r12*r31 - r13*r33*r22*r11 + sqr( r13 )*r31*r22 + r13 + r23*r11*r12*r33);  
		param[2] := (r11 - 1)*(r12*r33 - r32*r13) / (r23*r12*r31 + r33*r22*r11 - r13*r31*r22 - 1 - r32*r23*r11);  
		param[3] := 	(r12*r33 - r32*r13)*
			(sqr( r33 )*r22*r11 - r33*r13*r31*r22 - r33 - r33*r32*r23*r11 - r23*r12*r31 - r33*r22*r11 + r13*r31*r22 + 1 + r32*r23*r11 - sqr( r31 )*r13*r23*r12 - 
			  r31*r13*r33*r22*r11 + sqr( r31 )*sqr( r13 )*r22 + r31*r13 + r23*r11*r31*r12*r33 + r32*r13*r23*r31) / 
							(-r13*r23*r12*r31 - r13*r33*r22*r11 + sqr( r13 )*r31*r22 + r13 + r23*r11*r12*r33) / (r23*r12*r31 + r33*r22*r11 - r13*r31*r22 - 1 - r32*r23*r11);  
		param[4] := 	-(-r13*r23*r12*r31 - r13*r33*r22*r11 + sqr( r13 )*r31*r22 + r13 + r23*r11*r12*r33 - r12*r23*r33 + r23*r32*r13) / 
			(r23*r12*r31 + r33*r22*r11 - r13*r31*r22 - 1 - r32*r23*r11);  
		param[5] := (-r13*r23*r12*r31 - r13*r33*r22*r11 + sqr( r13 )*r31*r22 + r13 + r23*r11*r12*r33) / (r12*r33 - r32*r13);  
		param[6] := 	(r12*r33 - r32*r13)*
			(sqr( r12 )*sqr( r23 )*r31 + r12*r23*r33*r22*r11 - 2*r12*r23*r13*r31*r22 - r12*r23 - r12*sqr( r23 )*r32*r11 - r23*r11*r12*r33 + r12*r23*r33 - r23*r32*r13 - 
			  r13*sqr( r22 )*r33*r11 + sqr( r13 )*sqr( r22 )*r31 + r13*r22 + r13*r22*r32*r23*r11 + r13*r23*r12*r31 + r13*r33*r22*r11 - sqr( r13 )*r31*r22 - r13) / 
							(-r13*r23*r12*r31 - r13*r33*r22*r11 + sqr( r13 )*r31*r22 + r13 + r23*r11*r12*r33) / (r23*r12*r31 + r33*r22*r11 - r13*r31*r22 - 1 - r32*r23*r11);  
		param[7] := 	-(-r12*r13*r31*r22 + sqr( r12 )*r23*r31 - r12 - r12*r23*r32*r11 + r12*r33 - r32*r13 + r13*r22*r32*r11) / 
			(-r13*r23*r12*r31 - r13*r33*r22*r11 + sqr( r13 )*r31*r22 + r13 + r23*r11*r12*r33);  
		sos := param +* param;  
		IF (~Reals.IsNaNL(sos)) & ( sos < bestsos) THEN best := 3;  bestsos := sos;  bestparam := param END;  
		MatrixUtilities.OutVector( param );  out.Int(3, 4);  out.FloatFix(sos,12,6,1); out.Ln; CheckFactorization( param, 3 );  out.Ln;
		
		
		(* yzxy: *)
		param[0] := (-r31*r21*r32*r13 - r31*r33*r22*r11 + r31 + r13*sqr( r31 )*r22 + r32*r11*r21*r33) / (r32*r11 - r31*r12);  
		param[1] := 	(-r31*r21*r32*r13 - r31*r33*r22*r11 + r31 + r13*sqr( r31 )*r22 - r32*r11*r21 + r21*r31*r12 + r32*r11*r21*r33) / 
			(-r21*r32*r13 - r33*r22*r11 + 1 + r12*r21*r33 + r13*r31*r22);  
		param[2] := 	-(r32*r11 - r31*r12)*
			(r33*r22*sqr( r11 ) - r11 - r11*r12*r21*r33 - r11*r13*r31*r22 - r21*r32*r13 - r33*r22*r11 + 1 + r12*r21*r33 + r13*r31*r22 - r31*sqr( r13 )*r21*r32 - 
			  r31*r13*r33*r22*r11 + r31*r13 + sqr( r31 )*sqr( r13 )*r22 + r13*r21*r31*r12 + r13*r21*r33*r32*r11) / 
							(-r31*r21*r32*r13 - r31*r33*r22*r11 + r31 + r13*sqr( r31 )*r22 + r32*r11*r21*r33) / (-r21*r32*r13 - r33*r22*r11 + 1 + r12*r21*r33 + r13*r31*r22);  
		param[3] := -(-1 + r33)*(r32*r11 - r31*r12) / (-r21*r32*r13 - r33*r22*r11 + 1 + r12*r21*r33 + r13*r31*r22);  
		param[4] := 	(-r33*r22*sqr( r11 ) + r11 + r11*r12*r21*r33 + r11*r13*r31*r22 + r21*r32*r13 + r33*r22*r11 - 1 - r12*r21*r33 - r13*r31*r22 - r13*r21*r31*r12) / 
			(-r31*r21*r32*r13 - r31*r33*r22*r11 + r31 + r13*sqr( r31 )*r22 + r32*r11*r21*r33);  
		param[5] := -(-r21*r32*r13 - r33*r22*r11 + 1 + r12*r21*r33 + r13*r31*r22) / (r32*r11 - r31*r12);  
		param[6] := 	(r32*r13*r31*r22 - sqr( r32 )*r21*r13 + r32 + r32*r21*r12*r33 - r12*r33*r31*r22 - r32*r11 + r31*r12) / 
			(-r31*r21*r32*r13 - r31*r33*r22*r11 + r31 + r13*sqr( r31 )*r22 + r32*r11*r21*r33);  
		param[7] := 	(r32*r11 - r31*r12)*
			(-sqr( r32 )*sqr( r21 )*r13 - r32*r21*r33*r22*r11 + r32*r21 + r32*sqr( r21 )*r12*r33 + 2*r32*r21*r13*r31*r22 + r31*sqr( r22 )*r33*r11 - r31*r22 - 
			  r31*r22*r12*r21*r33 - sqr( r31 )*sqr( r22 )*r13 - r31*r21*r32*r13 - r31*r33*r22*r11 + r31 + r13*sqr( r31 )*r22 - r32*r11*r21 + r21*r31*r12 + r32*r11*r21*r33) / 
							(-r31*r21*r32*r13 - r31*r33*r22*r11 + r31 + r13*sqr( r31 )*r22 + r32*r11*r21*r33) / (-r21*r32*r13 - r33*r22*r11 + 1 + r12*r21*r33 + r13*r31*r22);  
		sos := param +* param;  
		IF (~Reals.IsNaNL(sos)) & ( sos < bestsos) THEN best := 4;  bestsos := sos;  bestparam := param END;  
		MatrixUtilities.OutVector( param );  out.Int(4, 4);  out.FloatFix(sos,12,6,1); out.Ln;  CheckFactorization( param, 4 );  out.Ln;
		
		(* zxyz: *)
		param[0] := 	(-r33*sqr( r22 )*r11 + r22 + r32*r22*r23*r11 + r22*r12*r21*r33 + r21*r32*r13 + r33*r22*r11 - 1 - r32*r23*r11 - r12*r21*r33 - r23*r12*r32*r21) / 
			(r13*r22*r32*r11 - r12*r21*r32*r13 - r12*r33*r22*r11 + r12 + sqr( r12 )*r21*r33);  
		param[1] := (-r21*r32*r13 - r33*r22*r11 + 1 + r32*r23*r11 + r12*r21*r33) / (-r13*r22 + r12*r23);  
		param[2] := 	(-r12*r21*r32*r13 - r12*r33*r22*r11 + r12 + sqr( r12 )*r21*r33 - r13*r22*r32 + r13*r22*r32*r11 + r32*r12*r23) / 
			(-r21*r32*r13 - r33*r22*r11 + 1 + r32*r23*r11 + r12*r21*r33);  
		param[3] := -(r13*r22*r32*r11 - r12*r21*r32*r13 - r12*r33*r22*r11 + r12 + sqr( r12 )*r21*r33) / (-r13*r22 + r12*r23);  
		param[4] := (r11 - 1)*(-r13*r22 + r12*r23) / (-r21*r32*r13 - r33*r22*r11 + 1 + r32*r23*r11 + r12*r21*r33);  
		param[5] := 	(-r13*r22 + r12*r23)*
			(r33*sqr( r22 )*r11 - r22 - r32*r22*r23*r11 - r22*r12*r21*r33 - r21*r32*r13 - r33*r22*r11 + 1 + r32*r23*r11 + r12*r21*r33 - r12*sqr( r21 )*r32*r13 - 
			  r12*r21*r33*r22*r11 + r12*r21 + sqr( r12 )*sqr( r21 )*r33 + r32*r11*r21*r13*r22 + r23*r12*r32*r21) / 
							(r13*r22*r32*r11 - r12*r21*r32*r13 - r12*r33*r22*r11 + r12 + sqr( r12 )*r21*r33) / (-r21*r32*r13 - r33*r22*r11 + 1 + r32*r23*r11 + r12*r21*r33);  
		param[6] := 	(-r13*r22 + r12*r23)*
			(sqr( r32 )*sqr( r13 )*r21 + r32*r13*r33*r22*r11 - r32*r13 - sqr( r32 )*r13*r23*r11 - 2*r32*r13*r12*r21*r33 - r12*sqr( r33 )*r22*r11 + r12*r33 + 
			  r12*r33*r32*r23*r11 + sqr( r12 )*sqr( r33 )*r21 + r12*r21*r32*r13 + r12*r33*r22*r11 - r12 - sqr( r12 )*r21*r33 - r13*r22*r32*r11 + r13*r22*r32 - r32*r12*r23) / 
							(r13*r22*r32*r11 - r12*r21*r32*r13 - r12*r33*r22*r11 + r12 + sqr( r12 )*r21*r33) / (-r21*r32*r13 - r33*r22*r11 + 1 + r32*r23*r11 + r12*r21*r33);  
		param[7] := 	-(-r13*r12*r21*r33 + r32*sqr( r13 )*r21 - r13 - r32*r13*r23*r11 + r23*r11*r12*r33 + r13*r22 - r12*r23) / 
			(r13*r22*r32*r11 - r12*r21*r32*r13 - r12*r33*r22*r11 + r12 + sqr( r12 )*r21*r33);  
		sos := param +* param;  
		IF (~Reals.IsNaNL(sos)) & ( sos < bestsos) THEN best := 5;  bestsos := sos;  bestparam := param END;  
		MatrixUtilities.OutVector( param );  
		out.Int(5, 4); out.FloatFix(sos,12,6,1); CheckFactorization( param, 5 );  out.Ln; 
		
		(* zyxz: *)
		param[0] := 	(-r21*r23*r12*r31 - r21*r33*r22*r11 + r21 + r12*sqr( r21 )*r33 - r31*r23*r11 + r13*r21*r31 + r31*r22*r23*r11) / 
			(-r23*r12*r31 - r33*r22*r11 + 1 + r13*r31*r22 + r12*r21*r33);  
		param[1] := (-r21*r23*r12*r31 - r21*r33*r22*r11 + r21 + r12*sqr( r21 )*r33 + r31*r22*r23*r11) / (r23*r11 - r13*r21);  
		param[2] := 	(-r33*r22*sqr( r11 ) + r11 + r11*r13*r31*r22 + r11*r12*r21*r33 + r23*r12*r31 + r33*r22*r11 - 1 - r13*r31*r22 - r12*r21*r33 - r13*r21*r31*r12) / 
			(-r21*r23*r12*r31 - r21*r33*r22*r11 + r21 + r12*sqr( r21 )*r33 + r31*r22*r23*r11);  
		param[3] := -(-r23*r12*r31 - r33*r22*r11 + 1 + r13*r31*r22 + r12*r21*r33) / (r23*r11 - r13*r21);  
		param[4] := 	-(r23*r11 - r13*r21)*
			(r33*r22*sqr( r11 ) - r11 - r11*r13*r31*r22 - r11*r12*r21*r33 - r23*r12*r31 - r33*r22*r11 + 1 + r13*r31*r22 + r12*r21*r33 - sqr( r12 )*r21*r23*r31 - 
			  r12*r21*r33*r22*r11 + r12*r21 + sqr( r12 )*sqr( r21 )*r33 + r13*r21*r31*r12 + r12*r31*r22*r23*r11) / 
							(-r21*r23*r12*r31 - r21*r33*r22*r11 + r21 + r12*sqr( r21 )*r33 + r31*r22*r23*r11) / (-r23*r12*r31 - r33*r22*r11 + 1 + r13*r31*r22 + r12*r21*r33);  
		param[5] := -(-1 + r22)*(r23*r11 - r13*r21) / (-r23*r12*r31 - r33*r22*r11 + 1 + r13*r31*r22 + r12*r21*r33);  
		param[6] := 	(r23*r12*r21*r33 - sqr( r23 )*r31*r12 + r23 + r23*r31*r13*r22 - r21*r33*r13*r22 - r23*r11 + r13*r21) / 
			(-r21*r23*r12*r31 - r21*r33*r22*r11 + r21 + r12*sqr( r21 )*r33 + r31*r22*r23*r11);  
		param[7] := 	-(r23*r11 - r13*r21)*
			(sqr( r23 )*sqr( r31 )*r12 + r23*r31*r33*r22*r11 - r23*r31 - r23*sqr( r31 )*r13*r22 - 2*r23*r31*r12*r21*r33 - r21*sqr( r33 )*r22*r11 + r21*r33 + 
			  r21*r33*r13*r31*r22 + sqr( r21 )*sqr( r33 )*r12 + r21*r23*r12*r31 + r21*r33*r22*r11 - r21 - r12*sqr( r21 )*r33 + r31*r23*r11 - r13*r21*r31 - r31*r22*r23*r11) / 
							(-r21*r23*r12*r31 - r21*r33*r22*r11 + r21 + r12*sqr( r21 )*r33 + r31*r22*r23*r11) / (-r23*r12*r31 - r33*r22*r11 + 1 + r13*r31*r22 + r12*r21*r33);  
		sos := param +* param;  
		IF (~Reals.IsNaNL(sos)) & ( sos < bestsos) THEN best := 6;  bestsos := sos;  bestparam := param END;  
		MatrixUtilities.OutVector( param );  out.Int(6, 4);  out.FloatFix(sos,12,6,1); out.Ln; CheckFactorization( param, 6 );  out.Ln; 
		
		MatrixUtilities.OutVector( bestparam );  out.Int(best,4); out.FloatFix(bestsos,12,6,1); out.Ln; out.Ln; 
		
		RETURN best;
	END Rotation4ShearDecomposition;  

	PROCEDURE Test*(context:Commands.Context);  
	VAR param: Vector;  best: SIGNED32;  
	BEGIN 
		best := Rotation4ShearDecomposition( EulerxyzToMatrix( 0, 3, 0.1 ), param );
		out.Ln; 
		out.String("best="); out.Int(best,4);
		out.Ln; out.Update;
	END Test;  

VAR out:Streams.Writer;
BEGIN
	Streams.OpenWriter(out, KernelLog.Send);
END ArrayRotations.

System.Free ArrayRotations ~
ArrayRotations.Test
OFormatter.Format *

Wikipedia:
The idea behind Euler angles is to split the complete rotation of the coordinate system into three simpler constitutive rotations, in such a way that the complete rotation matrix is the product of three simpler matrices. Notice that the outer matrix will represent a rotation around one of the axis of the reference frame, and the inner matrix represents a rotation around one of the moving frame axis. The middle matrix represent a rotation around an intermediate axis called line of nodes.

Unfortunately, the definition of Euler angles is not unique and in the literature many different conventions are used. These conventions depend on the axes about which the rotations are carried out, and their sequence (since rotations are not commutative).

The convention being used is usually indicated by specifying the axes about which the consecutive rotations (before being composed) take place, referring to them by index (1,2,3) or letter (X,Y,Z). The engineering and robotics communities typically use 3-1-3 Euler angles. Notice that after composing the independent rotations, they do not rotate about the axis anymore. The most external matrix rotates the other two, leaving the second rotation matrix over the line of nodes, and the third one in a frame comoving with the body. There are 3x3x3 := 27 possible definitions for Euler Anglerotations, but not all of them represent real decompositions.

Decomposition 
Rz := {cos(alpha) , sin(alpha) , 0 ;
(-sin(alpha)) , cos(alpha) , 0 ;
0 , 0 , 1}

Ry := {cos(theta) , 0 , sin(theta) ;
0 , 1 , 0 ;
(-sin(theta)) , 0 , cos(theta)}

Rx := {1 , 0 , 0 ;
0 , cos(phi) , sin(phi) ;
0 , (-sin(phi)) , cos(phi)}

Rotation Matrix Rz*Ry*Rx (implies 1) rotation phi around X; 2) rotation theta around Y, 3) rotation alpha around Z)
Rzyx := {(cos(alpha)*cos(theta)) , ((sin(alpha)*cos(phi))+(cos(alpha)*sin(theta)*(-sin(phi)))) , ((sin(alpha)*sin(phi))+(cos(alpha)*sin(theta)*cos(phi))) ;
((-sin(alpha))*cos(theta)) , ((cos(alpha)*cos(phi))+((-sin(alpha))*sin(theta)*(-sin(phi)))) , ((cos(alpha)*sin(phi))+((-sin(alpha))*sin(theta)*cos(phi))) ;
(-sin(theta)) , (cos(theta)*(-sin(phi))) , (cos(theta)*cos(phi))}



SxSySzSx:
Mx := {{1,0,0;a,1,0;b,0,1}}; 
My := {{1,c,0;0,1,0;0,d,1}}; 
Mz := {{1,0,e;0,1,f;0,0,1}}; 
M4 := {{1,0,0;g,1,0;h,0,1}}; 
M5 := Mx*My*Mz*M4;
output:
Sxyzx := {(1+(c*g)+((e+(c*f))*h)) , c , (e+(c*f)) ;
(a+((1+(a*c))*g)+(((a*e)+((1+(a*c))*f))*h)) , (1+(a*c)) , ((a*e)+((1+(a*c))*f)) ;
(b+(((b*c)+d)*g)+((1+(b*e)+(((b*c)+d)*f))*h)) , ((b*c)+d) , (1+(b*e)+(((b*c)+d)*f))}

SxSzSySx:
Mx := {{1,0,0;a,1,0;b,0,1}}; 
My := {{1,c,0;0,1,0;0,d,1}}; 
Mz := {{1,0,e;0,1,f;0,0,1}}; 
M4 := {{1,0,0;g,1,0;h,0,1}}; 
M5 := Mx*Mz*My*M4;
M5 := {(1+((c+(e*d))*g)+(e*h)) , (c+(e*d)) , e ;
(a+((1+(a*c)+(((a*e)+f)*d))*g)+(((a*e)+f)*h)) , (1+(a*c)+(((a*e)+f)*d)) , ((a*e)+f) ;
(b+(((b*c)+((1+(b*e))*d))*g)+((1+(b*e))*h)) , ((b*c)+((1+(b*e))*d)) , (1+(b*e))}

SySxSzSy:
Mx := {{1,0,0;a,1,0;b,0,1}}; 
My := {{1,c,0;0,1,0;0,d,1}}; 
Mz := {{1,0,e;0,1,f;0,0,1}}; 
My2 := {{1,g,0;0,1,0;0,h,1}}; 
M := My*Mx*Mz*My2;
Syxzy := {(1+(c*a)) , (((1+(c*a))*g)+c+((((1+(c*a))*e)+(c*f))*h)) , (((1+(c*a))*e)+(c*f)) ;
a , (1+(a*g)+(((a*e)+f)*h)) , ((a*e)+f) ;
((d*a)+b) , ((((d*a)+b)*g)+d+((1+(((d*a)+b)*e)+(d*f))*h)) , (1+(((d*a)+b)*e)+(d*f))}

SySzSxSy:
Mx := {{1,0,0;a,1,0;b,0,1}}; 
My := {{1,c,0;0,1,0;0,d,1}}; 
Mz := {{1,0,e;0,1,f;0,0,1}}; 
My2 := {{1,g,0;0,1,0;0,h,1}}; 
Syzxz := My*Mz*Mx*My2;
Syzxz := {(1+(c*a)+((e+(c*f))*b)) , (((1+(c*a)+((e+(c*f))*b))*g)+c+((e+(c*f))*h)) , (e+(c*f)) ;
(a+(f*b)) , (1+((a+(f*b))*g)+(f*h)) , f ;
((d*a)+((1+(d*f))*b)) , ((((d*a)+((1+(d*f))*b))*g)+d+((1+(d*f))*h)) , (1+(d*f))}

SzSxSySz:
Mx := {1,0,0;a,1,0;b,0,1}; 
My := {1,c,0;0,1,0;0,d,1}; 
Mz := {1,0,e;0,1,f;0,0,1}; 
My2 := {1,g,0;0,1,0;0,h,1}; 
Mz2 := {1,0,g;0,1,h;0,0,1}; 
Szxyz := Mz*Mx*My*Mz2;
Szxyz := {(1+(e*b)) , (((1+(e*b))*c)+(e*d)) , (((1+(e*b))*g)+((((1+(e*b))*c)+(e*d))*h)+e) ;
(a+(f*b)) , (1+((a+(f*b))*c)+(f*d)) , (((a+(f*b))*g)+((1+((a+(f*b))*c)+(f*d))*h)+f) ;
b , ((b*c)+d) , (1+(b*g)+(((b*c)+d)*h))}

SzSySxSz:
Mx := {1,0,0;a,1,0;b,0,1}; 
My := {1,c,0;0,1,0;0,d,1}; 
Mz := {1,0,e;0,1,f;0,0,1}; 
My2 := {1,g,0;0,1,0;0,h,1}; 
Mz2 := {1,0,g;0,1,h;0,0,1}; 
Szyxz := {(1+((c+(e*d))*a)+(e*b)) , (c+(e*d)) , (((1+((c+(e*d))*a)+(e*b))*g)+((c+(e*d))*h)+e) ;
(((1+(f*d))*a)+(f*b)) , (1+(f*d)) , (((((1+(f*d))*a)+(f*b))*g)+((1+(f*d))*h)+f) ;
((d*a)+b) , d , (1+(((d*a)+b)*g)+(d*h))}

