from norine_general_pysat import *
import time
from subprocess import TimeoutExpired, check_output, CalledProcessError, STDOUT
import matplotlib.pyplot as plt

def system_call(command, timeout=None):
    """
    params:
        command: list of strings, ex. ["ls", "-l"]
        timeout: number of seconds to wait for the command to complete.
    returns: output, return_code
    """
    try:
        cmd_output = check_output(command, stderr=STDOUT, timeout=timeout).decode()
        return_code = 0
    except CalledProcessError as e:
        cmd_output = e.output.decode()
        return_code = e.returncode
    except TimeoutExpired:
        cmd_output = f"Command timed out after {timeout} seconds"
        return_code = (
            -1
        )  # You can use any number that is not a valid return code for a success or normal failure
    return cmd_output, return_code


def timed_run_shell(commands, timeout=None):
    """
    params:
        command: list of strings, ex. ["ls", "-l"]
        timeout: number of seconds to wait for the command to complete.
    returns: output, return_code, elapsed_time in mseconds
    """
    start_time = time.perf_counter_ns()
    output, return_code = system_call(commands, timeout=timeout)
    elapsed_time = time.perf_counter_ns() - start_time
    return output, return_code, elapsed_time / 1e9

def symmetry_breaking_experiment():
    """
    Run an experiment to evaluate the impact of symmetry breaking on solving time.
    """
    n = 7

    data = {}
    for sb in range(0, 51, 1):
        encoding, var_to_edge = encode(n, sum_upper_bound=None, antipodal=True, partial_sym_break=sb,
                                        conjecture1=True)
        
        encoding.to_file(f"norine_{n}_sb{sb}.cnf")
        print(f"Encoding size: {len(encoding.clauses)} clauses")
        times = []
        for m in range(0):
            print(f"Running kissat on norine_{n}_sb{sb}.cnf...")
            timed_run_shell(["scranfilize", "-P", f"norine_{n}_sb{sb}.cnf", f"scranf_{n}_sb{sb}.cnf", "-f", "0", "--force"])
            output, return_code, elapsed_time = timed_run_shell(
                ["kissat", f"scranf_{n}_sb{sb}.cnf"],
                timeout=120
            )
            print(f"Return code: {return_code}, Elapsed time: {elapsed_time} seconds")
            times.append(elapsed_time)
        data[sb] = (len(encoding.clauses), times)

    print(f"Encoding size: {data} clauses")
    return data

def symmetry_breaking_plot(data):
    
    fig, ax1 = plt.subplots()
    sb_values = list(data.keys())
    sizes = [data[sb][0] for sb in sb_values]
    times = [data[sb][1] for sb in sb_values]
    def process_times(time):
        if type(time) is list:
            return sum(time) / len(time) if time else 0
        return time
    times = [process_times(t) for t in times]

    color1 = 'tab:blue'
    ax1.set_xlabel('Symmetry Breaking Parameter')
    ax1.set_ylabel('Encoding size', color=color1)
    ax1.plot(sb_values, sizes, color=color1, marker='o')
    ax1.tick_params(axis='y', labelcolor=color1)

    ax2 = ax1.twinx()  

    # 4) plot g(n) on the right y‐axis:
    color2 = 'tab:red'
    ax2.set_ylabel('Solving time', color=color2)
    ax2.plot(sb_values, times, color=color2, marker='s')
    ax2.tick_params(axis='y', labelcolor=color2)
    plt.legend()
    plt.grid(True)
    plt.show()


if __name__ == "__main__":
    # symmetry_breaking_experiment()
    data = symmetry_breaking_experiment()
    baseline = data[0][0]
    for sb in data:
        print(f"({sb}, {data[sb][0] - baseline})")
    # print(f"Data collected: {data}")
    # data = {5: (70015, 42.750967), 10: (72535, 34.687453042), 15: (75055, 26.235423792), 20: (77575, 35.724139667), 25: (80095, 29.032216208), 30: (82615, 27.272516209), 35: (85135, 26.950659083), 40: (87655, 29.05652025), 45: (90175, 36.844700625)}
    # symmetry_breaking_plot(data)
