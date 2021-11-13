from ipykernel.kernelbase import Kernel
import pexpect, os

class EchoKernel(Kernel):
    implementation = 'Echo'
    implementation_version = '1.0'
    language = 'no-op'
    language_version = '0.1'
    language_info = {'mimetype': 'text/plain'}
    banner = "Echo kernel - as useful as a parrot"

    def do_execute(self, code, silent, store_history=True, user_expressions=None,
                   allow_stdin=False):
        if not silent:
            if not hasattr(self,"oruga_runner"):
                self.oruga_runner = OrugaRunner()
            stream_content = {'name': 'stdout', 'text': self.oruga_runner.run(code)}
            self.send_response(self.iopub_socket, 'stream', stream_content)

        return {'status': 'ok',
                # The base class increments the execution count
                'execution_count': self.execution_count,
                'payload': [],
                'user_expressions': {},
               }

class OrugaRunner():

    def __init__(self):
        os.chdir("..")
        self.subprocess = pexpect.spawnu("make repl")
        self.subprocess.expect(pexpect.EOF)
        self.subprocess.sendline('import "oruga/document";')

    def run(self, code):
        self.subprocess.sendline(code)
        self.subprocess.expect(pexpect.EOF)
        print("HELLOO")
        return self.subprocess.before


if __name__ == '__main__':
    from ipykernel.kernelapp import IPKernelApp
    IPKernelApp.launch_instance(kernel_class=EchoKernel)