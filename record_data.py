import os
import subprocess
from collections import defaultdict
import time
import json
import argparse

# Store the solving time of a configuration in stats_dict.
def record_data(config, flags, files, solver, timeout):  
    stats_dict = defaultdict(list)
    # Print the current progress on the console.
    print("\n"+config)
    print("==============")
    for i, f in enumerate(files):
        print(f'solving {i+1}/{len(files)}: {os.path.basename(f)}')
        start = time.time()
        try:
            subprocess.run([solver, *flags, f], stdout=subprocess.DEVNULL, timeout = timeout)
            end = time.time()
            print("%.4fs" % (end-start))
            stats_dict[config].append(end-start)
        except subprocess.TimeoutExpired:
            print("timeout")
    return stats_dict

        
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Records solver runtime.")
    parser.add_argument('solver', help='path to solver')
    parser.add_argument('timeout', help='timeout for each formula', type=int)
    parser.add_argument('write_to', help='the file to write results to')
    parser.add_argument('benchmarks', help='benchmarks to be tested', nargs='+')
    args, unknown_args = parser.parse_known_args()

    # Only create a new file when the given file does not exist yet.
    if not os.path.isfile(args.write_to): 
        with open(args.write_to, 'w') as f:
                name = os.path.splitext(os.path.basename(args.write_to))[0]
                print("forward these to solver:", *unknown_args)
                f.write(json.dumps(record_data(name, unknown_args, args.benchmarks, args.solver, args.timeout)))
    else:
        print(args.write_to, "already exists.")