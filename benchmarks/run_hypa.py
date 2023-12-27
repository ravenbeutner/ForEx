import subprocess
from subprocess import TimeoutExpired
import sys
import time

def system_call(cmd : str, timeout_sec=None):
    
    proc = subprocess.Popen(cmd, shell=True, stderr=subprocess.PIPE, stdout=subprocess.PIPE)

    try:
        stdout, stderr = proc.communicate(timeout=timeout_sec)
    except TimeoutExpired:
        proc.kill()
        return None, "", ""
   
    return proc.returncode, stdout.decode("utf-8").strip(), stderr.decode("utf-8").strip()

def call_forex(instance_path : str, timeout : int):
    args = [
        '../app/ForEx',
        instance_path
    ]

    startTime = time.time()
    (code, out, err) = system_call(' '.join(args), timeout_sec=timeout)
    endTime = time.time()
    et = endTime - startTime 

    if code == None:
        return None

    if code != 0 or err != "": 
        print ("Error by ForEx: ", err, out, err, file=sys.stderr)
        return None
    
    if 'UNSAT' in out:
        res = False 
    else:
        assert ('SAT' in out)
        res = True
    
    return {'time': et, 'res': res}


instances_hypa = [
    {
        'name': 'non_det_add',
        'path': 'hypa/non_det_add.txt'
    },

    {
        'name': 'counter_sum',
        'path': 'hypa/counter_sum.txt'
    },

    {
        'name': 'asynch_gni',
        'path': 'hypa/asynch_gni.txt'
    },

    {
        'name': 'compiler_opt',
        'path': 'hypa/compiler_opt.txt'
    },

    {
        'name': 'compiler_opt2',
        'path': 'hypa/compiler_opt2.txt'
    },

    {
        'name': 'refine',
        'path': 'hypa/refine.txt'
    },

    {
        'name': 'refine2',
        'path': 'hypa/refine2.txt'
    },

    {
        'name': 'smaller',
        'path': 'hypa/smaller.txt'
    },

    {
        'name': 'counter_diff',
        'path': 'hypa/counter_diff.txt'
    },

    {
        'name': 'paper_example_fig3',
        'path': 'hypa/paper_example_fig3.txt'
    },

    {
        'name': 'p1_gni',
        'path': 'hypa/p1_gni.txt'
    },

    {
        'name': 'p2_gni',
        'path': 'hypa/p2_gni.txt'
    },

    {
        'name': 'p3_gni',
        'path': 'hypa/p3_gni.txt'
    },

    {
        'name': 'p4_gni',
        'path': 'hypa/p4_gni.txt'
    }
]

for i in instances_hypa:
    print('========================================================')
    print('Instance:', i['name'])

    res = call_forex(instance_path=i['path'], timeout=3600)

    if res == None:
        print('TO')
    else:
        print('Time: ', res['time'], 'seconds')
    print('========================================================\n')
