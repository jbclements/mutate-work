import json
import re
import sys

def process_mutation_output(file_path, test_file):
    with open(file_path, 'r') as file:
        content = file.read()

    # Regular expressions to match lines in the output file
    num_mutant_pattern = re.compile(r'/#:NUM MUTANT: (\d+):#/')
    mutator_pattern = re.compile(r'/#:MUTANT USED: \((.*?)\):#/')
    result_pattern = re.compile(r'MUTANT_RESULT: (passed|failed)')

    # Split the content by the custom delimiter
    entries = content.split('//##::##//')
    # print(len(entries))
    mutation_results = []
    mutation_score = None

    for entry in entries:
        # print(entry)
        num_mutant_match = num_mutant_pattern.search(entry)
        # print(num_mutant_match, "num_mutant")
        mutator_match = mutator_pattern.search(entry)
        # print(mutator_match, "mutator")
        result_match = result_pattern.search(entry)
        # print(result_match, "result")
        score_match = re.search(r'Mutation score: (\d+\.\d+)', entry)

        if num_mutant_match and mutator_match and result_match:
            mutation_results.append({
                "NumMutant": int(num_mutant_match.group(1)),
                "MutatorType": mutator_match.group(1),
                "Result": result_match.group(1)
            })

        if score_match:
            mutation_score = float(score_match.group(1))

    # Prepare the final JSON structure
    json_data = {
        "MutationResults": mutation_results,
        "MutationScore": mutation_score,
        "TestFile": test_file
    }

    return json_data

def write_to_json(data, output_file):
    with open(output_file, 'w') as file:
        json.dump(data, file, indent=4)

if __name__ == "__main__":
    #  read command line arguments
    command_line_args = sys.argv
    if len(command_line_args) != 3:
        # print(command_line_args)
        print("Usage: python parse-output.py <tested-file> <output-file>")
        sys.exit(1)
    else:
        test_file = command_line_args[1]
        output_file_path = command_line_args[2]

    input_file_path = "mutant-output.txt"  # Path to the output file
    # output_file_path = "mutation_results.json"  # Path to the JSON output file
    
    mutation_data = process_mutation_output(input_file_path, test_file)
    write_to_json(mutation_data, output_file_path)

    print(f"Mutation results have been written to {output_file_path}")
