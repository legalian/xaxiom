import os
if "Sublime Text" not in __file__:
  from flask import Flask, request
  from flask import got_request_exception
  import rollbar
  import rollbar.contrib.flask

  APP = Flask(__name__)

  @APP.route('/verify', methods=["POST"])
  def _verify():
    return request.get_json()

  rollbar.init(
    'f7207c6c132743f2b1c29dfed3e00129',
    'production',
    root=os.path.dirname(os.path.realpath(__file__)),
    allow_logging_basic_config=False)

  got_request_exception.connect(rollbar.contrib.flask.report_exception, APP)

  # We only need this for local development.
  if __name__ == '__main__':
    APP.run()
