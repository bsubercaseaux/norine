import argparse
import random

random.seed(42)  # for reproducibility
argparser = argparse.ArgumentParser(description="Norine general encoding with pysat")
argparser.add_argument("-i", "--input", type=str, help="Input file with cubes", required=True)
argparser.add_argument('-c', '--cubes', type=int, help="Number of cubes to sample", default=100)

args = argparser.parse_args()
input_file = args.input
cubes_to_sample = args.cubes

to_write = []
cubes = []
with open(input_file, 'r') as f:
    for line in f:
        if line.startswith('a'):
            cubes.append([int(x) for x in line.strip().split()[1:-1]])
        else:
            to_write.append(line.strip())

selected_cubes = random.sample(cubes, min(cubes_to_sample, len(cubes)))
for cube in selected_cubes:
    to_write.append('a ' + ' '.join(map(str, cube)) + ' 0')

output_file = "sampled_" + input_file

with open(output_file, 'w') as f:
    f.write('\n'.join(to_write) + '\n')

print(f"Sampled {len(selected_cubes)} cubes from {input_file} and saved to {output_file}.")