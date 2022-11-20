#!/usr/bin/env python3
import asyncio
import sys
from asyncio.subprocess import PIPE, STDOUT

async def run_command(*args, timeout=None):
    # start child process
    # NOTE: universal_newlines parameter is not supported
    process = await asyncio.create_subprocess_exec(*args,stdout=PIPE, stderr=STDOUT)
    print(*args)
    # read line (sequence of bytes ending with b'\n') asynchronously
    while True:
        try:
            line = await asyncio.wait_for(process.stdout.readline(), timeout)
        except asyncio.TimeoutError:
            print('=== Timeout occured ===')
            pass
        else:
            if not line: # EOF
                break
          # elif do_something(line):
            else:
                print(line.decode('CP866'))
                continue # while some criterium is satisfied
        process.kill() # timeout or some criterium is not satisfied
        break
    return await process.wait() # wait for the child process to exit


mytimeout = 1
# command = 'c:\\adb\\adb.exe shell /data/local/tmp/iperf3.7 -v'
# arg_1 = "devices"
arg_1 = "shell"
# arg_2 = "-l"
arg_2 = "/data/local/tmp/iperf3.7 -s -p5008"
# command = 'cmd dir c:\\'
command = 'c:\\adb\\adb.exe'
if sys.platform == "win32":
    loop = asyncio.ProactorEventLoop() # for subprocess' pipes on Windows
    asyncio.set_event_loop(loop)
else:
    loop = asyncio.get_event_loop()

returncode = loop.run_until_complete(run_command(command, arg_1, arg_2, timeout=mytimeout))
print(f'returncode={returncode}')
loop.close()