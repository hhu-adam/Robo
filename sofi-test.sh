time="$(date +"%Y-%m-%d--%H-%M-%S")"
testdir="sofi-test_${time}"
cp -r ./sofi-test-data ./$testdir
echo -e "\nTEST1: Running sofi.sh without a parameter should result in a error."
./sofi.sh
echo -e "\nTEST2: Running sofi.sh with a folder as parameter that is not nested below /Game/Levels should result in an error."
./sofi.sh "./${testdir}/Game"
echo -e "\nTEST3: Running sofi.sh with a file as parameter should result in an error."
./sofi.sh "./${testdir}/Game/Levels/Test.lean"
echo -e "\nTEST4 (Correct usage of sofi.sh):"
./sofi.sh "./${testdir}/Game/Levels/Test"
