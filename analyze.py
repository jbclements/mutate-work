import pandas as pd
from matplotlib import pyplot as plt


df = pd.read_csv('mutation_report.csv')

# convert Result column to boolean
df['survived'] = df['Result'].map({'failed': False, 'passed': True})
# group by mutant type and plot mean of survived mutants
df.groupby('MutatorType').survived.mean().plot(kind='bar')

# add another plot to the same figure, with the total number of mutants
df.MutatorType.value_counts().plot(kind='line', color='red', secondary_y=True)
plt.ylabel('Number of mutants')
plt.show()