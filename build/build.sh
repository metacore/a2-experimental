path=$1
rm -rf $path
mkdir $path
if [[ $path =~ Linux.* ]]; then
	cp Linux/* $path
fi
if [[ $path =~ Win.* ]]; then
	cp Win/* $path
fi
mkdir $path/work
mkdir $path/bin
../Linux64/oberon do "
System.DoFile oberon.ini ~
Files.SetWorkPath $path ~
System.DoFile ../$path.txt ~
"
result=$?
if (( result==0 )); then
	rm -f $path/bin/CompileCommand.Tool
	rm -f $path/oberon.log
	chmod +x $path/oberon*
	zip -rq $path.zip $path
	mv $path.zip ..
	#rm -r $path
else
	rm -r $path
	echo "not successfull!!!"
	exit 1
fi
