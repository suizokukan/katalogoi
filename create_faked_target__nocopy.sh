# NB : the --configfile option is given in order to preempt an eventual
#      configuration file in ~/.katal/katal.ini  .

echo
echo "(01) rm -rf faked/target"
rm -rf faked/target

echo
echo "(02) rm -rf faked/src2"
rm -rf faked/src2

echo
echo "(03) cp -r faked/src faked/src2"
cp -r faked/src faked/src2

echo
echo "(04) ./katal/katal.py --new=faked/target --verbosity=none"
./katal/katal.py --new=faked/target --verbosity=none

echo
echo "(05) cp faked/katal.nocopy.ini faked/target/.katal/katal.ini"
cp faked/katal.nocopy.ini faked/target/.katal/katal.ini

echo
echo "(06) cd faked/target"
cd faked/target

echo
echo "(07) ../../katal/katal.py --add --strictcmp --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --add --strictcmp --configfile=../../faked/target/.katal/katal.ini

echo
echo "(08) ../../katal/katal.py --addtag=goose --to=*5.py --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --addtag=goose --to=*5.py --configfile=../../faked/target/.katal/katal.ini

echo
echo "(09) ../../katal/katal.py --addtag=tree --to=*9.py --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --addtag=tree --to=*9.py --configfile=../../faked/target/.katal/katal.ini

echo
echo "(10) ../../katal/katal.py --addtag=pink --to=*1*.py --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --addtag=pink --to=*1*.py --configfile=../../faked/target/.katal/katal.ini

echo
echo "(11) ../../katal/katal.py --rmnotag --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --rmnotag --configfile=../../faked/target/.katal/katal.ini

echo
echo "(15) ../../katal/katal.py --rmtags --to=10.py --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --rmtags --to=10.py --configfile=../../faked/target/.katal/katal.ini

echo
echo "(16) ../../katal/katal.py --findtag=goose --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --findtag=goose --configfile=../../faked/target/.katal/katal.ini

echo
echo "(17) ../../katal/katal.py --settagsstr="red;marble" --to=13.py --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --settagsstr="red;marble" --to=13.py --configfile=../../faked/target/.katal/katal.ini

echo
echo "(18) ../../katal/katal.py --findtag=pink --copyto=xyz --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py --findtag=pink --copyto=xyz --configfile=../../faked/target/.katal/katal.ini

echo
echo "(19) ../../katal/katal.py -ti --configfile=../../faked/target/.katal/katal.ini"
../../katal/katal.py -ti --configfile=../../faked/target/.katal/katal.ini
