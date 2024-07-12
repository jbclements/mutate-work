args=("$@")
# Create a report directory
mkdir -p "report"
DIRECTORY="program3"
TOTAL_FILES=$(ls $DIRECTORY/*.rkt | wc -l)
START_TIME=$(date +%s)

file_count=0

for file in $DIRECTORY/*.rkt;
do
    file_count=$((file_count + 1))
    echo "Running $file"
    
    FILE_START_TIME=$(date +%s)
    
    racket "mutation-tester.rkt" "$file"
    
    FILENAME=$(basename "$file")
    FILENAME="${FILENAME%.*}.json"
    
    python3 "parse-output.py" "$file" "report/$FILENAME"
    
    FILE_END_TIME=$(date +%s)
    FILE_DURATION=$((FILE_END_TIME - FILE_START_TIME))
    
    TOTAL_DURATION=$((FILE_END_TIME - START_TIME))
    AVERAGE_DURATION=$((TOTAL_DURATION / file_count))
    REMAINING_FILES=$((TOTAL_FILES - file_count))
    ESTIMATED_REMAINING_TIME=$((REMAINING_FILES * AVERAGE_DURATION))
    
    echo "Processed $file_count/$TOTAL_FILES files. Estimated remaining time: $ESTIMATED_REMAINING_TIME seconds."
done
