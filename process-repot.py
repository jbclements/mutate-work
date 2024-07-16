import pandas as pd
import os
import json

dfs = []
# read the data from the report direcotry
for file in os.listdir('report'):
    if file.endswith('.json'):
        data = json.load(open('report/' + file))
        csv_data = data["MutationResults"]
        df = pd.DataFrame(csv_data)
        df["file"] = data["TestFile"]
        df["mutation_score"] = data["MutationScore"]
        dfs.append(df)

# combine all the data into one dataframe
df = pd.concat(dfs, ignore_index=True)
# save the data to a csv file
df.to_csv('mutation_report.csv', index=False)