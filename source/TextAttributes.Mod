MODULE TextAttributes;
IMPORT Configuration, Texts, WMGraphics;

TYPE
	FontInfo* = Texts.FontInfo;
	Attributes* = Texts.Attributes;

PROCEDURE GetDefaultAttributes* () : Attributes;
VAR
	defaultAttributes 			: Attributes;
	font 						: WMGraphics.Font;
	textColor, textBackColor	: LONGINT;
	res 						: LONGINT;
BEGIN
	NEW( defaultAttributes );
	Configuration.GetColor( "WindowManager.DefaultColor.TextBackColor", textBackColor, res );
	IF res # Configuration.Ok THEN textBackColor := 0H; END; (* transparent *)
	Configuration.GetColor( "WindowManager.DefaultColor.TextColor", textColor, res );
	IF res # Configuration.Ok THEN textColor := 0FFH; END; (* black *)
	font := WMGraphics.GetDefaultFont( );
	defaultAttributes.Set( textColor, textBackColor, 0, font.name, font.size, font.style );
	RETURN defaultAttributes
END GetDefaultAttributes;

END TextAttributes.