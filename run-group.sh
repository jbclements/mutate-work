args=("$@")
# Create a report directory
mkdir -p "report"
DIRECTORY="program2"
for file in $DIRECTORY/*.rkt;
do
    echo "Running $file"
    racket "charlie-mutation-tester.rkt" "$file"
    # parse-output expects an ourput file as an argument, create the output file the same name as the input file but in the report directory
    FILENAME=$(basename "$file")
    # rename from .rkt to .json
    FILENAME="${FILENAME%.*}.json"
    python3 "parse-output.py" "$file" "report/$FILENAME"
done