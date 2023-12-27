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



instances_pcsat = [
    {
        'name': 'TI_GNI_hFF',
        'path': 'pcsat/TI_GNI_hFF.txt'
    },

    {
        'name': 'TI_GNI_hTT',
        'path': 'pcsat/TI_GNI_hTT.txt'
    },

    {
        'name': 'TI_GNI_hFT',
        'path': 'pcsat/TI_GNI_hFT.txt'
    },

    {
        'name': 'TS_GNI_hFF',
        'path': 'pcsat/TS_GNI_hFF.txt'
    },

    {
        'name': 'TS_GNI_hTT',
        'path': 'pcsat/TS_GNI_hTT.txt'
    },

    {
        'name': 'TS_GNI_hFT',
        'path': 'pcsat/TS_GNI_hFT.txt'
    }
]


for i in instances_pcsat:
    print('========================================================')
    print('Instance:', i['name'])

    res = call_forex(instance_path=i['path'], timeout=3600)

    if res == None:
        print('TO')
    else:
        print('Time: ', res['time'], 'seconds')
    print('========================================================\n')

