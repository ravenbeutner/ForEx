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



instances_k_safety = [
    {
        'name': 'double_square_ni',
        'path': 'k_safety/double_square_ni.txt'
    },

    {
        'name': 'exp1x3',
        'path': 'k_safety/exp1x3.txt'
    },

    {
        'name': 'fig3',
        'path': 'k_safety/fig3.txt'
    },

    {
        'name': 'double_square_ni',
        'path': 'k_safety/double_square_ni_ff.txt'
    }, 

    {
        'name': 'fig2',
        'path': 'k_safety/fig2.txt'
    }, 

    {
        'name': 'coll_item_sym',
        'path': 'k_safety/coll_item_sym.txt'
    }, 

    {
        'name': 'counter_det',
        'path': 'k_safety/counter_det.txt'
    }, 

    {
        'name': 'mult_equiv',
        'path': 'k_safety/mult_equiv.txt'
    }
]


for i in instances_k_safety:
    print('========================================================')
    print('Instance:', i['name'])

    res = call_forex(instance_path=i['path'], timeout=3600)

    if res == None:
        print('TO')
    else:
        print('Time: ', res['time'], 'seconds')
    print('========================================================\n')

