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


instances_hypro = [
    {
        'bitwidth': 1, 
        'instances':
            [
                'hypro/p1_1bit.txt',
                'hypro/p2_1bit.txt',
                'hypro/p3_1bit.txt',
                'hypro/p4_1bit.txt',
            ]
    },
    {
        'bitwidth': 2, 
        'instances':
            [
                'hypro/p1_2bit.txt',
                'hypro/p2_2bit.txt',
                'hypro/p3_2bit.txt',
                'hypro/p4_2bit.txt',
            ]
    },
    {
        'bitwidth': 3, 
        'instances':
            [
                'hypro/p1_3bit.txt',
                'hypro/p2_3bit.txt',
                'hypro/p3_3bit.txt',
                'hypro/p4_3bit.txt',
            ]
    },
    {
        'bitwidth': 4, 
        'instances':
            [
                'hypro/p1_4bit.txt',
                'hypro/p2_4bit.txt',
                'hypro/p3_4bit.txt',
                'hypro/p4_4bit.txt',
            ]
    },
    {
        'bitwidth': 5, 
        'instances':
            [
                'hypro/p1_5bit.txt',
                'hypro/p2_5bit.txt',
                'hypro/p3_5bit.txt',
                'hypro/p4_5bit.txt',
            ]
    },
    {
        'bitwidth': 6, 
        'instances':
            [
                'hypro/p1_6bit.txt',
                'hypro/p2_6bit.txt',
                'hypro/p3_6bit.txt',
                'hypro/p4_6bit.txt',
            ]
    }
]

for bucket in instances_hypro:
    print('========================================================')
    print('Bitwidth:', bucket['bitwidth'])

    for path in bucket['instances']:
        res = call_forex(instance_path=path, timeout=3600)

        if res == None:
            print('TO')
        else:
            print('Time: ', res['time'], 'seconds')
    print('========================================================\n')
