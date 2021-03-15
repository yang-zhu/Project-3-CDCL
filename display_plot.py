from collections import defaultdict
import json
import seaborn as sns
import matplotlib.pyplot as plt
import argparse

parser = argparse.ArgumentParser(description="Displays cactus plots.")
parser.add_argument('files', help='data files to display', nargs='+')
parser.add_argument('-logscale', help='display time in logscale', action='store_true')
args = parser.parse_args()

# Combine the stats from several files.
stats_combined = defaultdict(list)
for file in args.files:
    with open(file, 'r') as f:
        stats_part = json.loads(f.read())
        for conf in stats_part:
            stats_combined[conf] += stats_part[conf]

# Convert the structure of stats_combined for seaborn.
stats_dict = defaultdict(list)
for conf in stats_combined:
    runtimes = sorted(stats_combined[conf])
    for i, runtime in enumerate(runtimes):
        stats_dict['Configuration'].append(conf)
        stats_dict['Instances'].append(i+1)
        stats_dict['Time'].append(runtime)

# Display the cactus plot.
fig, axs = plt.subplots(ncols=1)
fig.canvas.set_window_title('Evaluation')
markers = ['o']*len(stats_combined)
colors = sns.color_palette('bright')[:len(stats_combined)]
sns.lineplot(x='Instances', y='Time', hue='Configuration', data=stats_dict, markers=markers, style="Configuration", dashes=False, palette=colors)
axs.set(xlabel = 'number of solved instances', ylabel = 'CPU time (s)')
if args.logscale:
    plt.yscale('log')
plt.show()