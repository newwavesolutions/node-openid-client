"use strict";

function asyncGeneratorStep(gen, resolve, reject, _next, _throw, key, arg) { try { var info = gen[key](arg); var value = info.value; } catch (error) { reject(error); return; } if (info.done) { resolve(value); } else { Promise.resolve(value).then(_next, _throw); } }

function _asyncToGenerator(fn) { return function () { var self = this, args = arguments; return new Promise(function (resolve, reject) { var gen = fn.apply(self, args); function _next(value) { asyncGeneratorStep(gen, resolve, reject, _next, _throw, "next", value); } function _throw(err) { asyncGeneratorStep(gen, resolve, reject, _next, _throw, "throw", err); } _next(undefined); }); }; }

/* eslint-disable camelcase */
const {
  inspect
} = require('util');

const {
  RPError,
  OPError
} = require('./errors');

const instance = require('./helpers/weak_cache');

const now = require('./helpers/unix_timestamp');

const {
  authenticatedPost
} = require('./helpers/client');

const processResponse = require('./helpers/process_response');

const TokenSet = require('./token_set');

class DeviceFlowHandle {
  constructor({
    client,
    exchangeBody,
    clientAssertionPayload,
    response,
    maxAge
  }) {
    ['verification_uri', 'user_code', 'device_code'].forEach(prop => {
      if (typeof response[prop] !== 'string' || !response[prop]) {
        throw new RPError(`expected ${prop} string to be returned by Device Authorization Response, got %j`, response[prop]);
      }
    });

    if (!Number.isSafeInteger(response.expires_in)) {
      throw new RPError('expected expires_in number to be returned by Device Authorization Response, got %j', response.expires_in);
    }

    instance(this).expires_at = now() + response.expires_in;
    instance(this).client = client;
    instance(this).maxAge = maxAge;
    instance(this).exchangeBody = exchangeBody;
    instance(this).clientAssertionPayload = clientAssertionPayload;
    instance(this).response = response;
    instance(this).interval = response.interval * 1000 || 5000;
  }

  poll() {
    var _this = this;

    return _asyncToGenerator(function* () {
      if (_this.expired()) {
        throw new RPError('the device code %j has expired and the device authorization session has concluded', _this.device_code);
      }

      yield new Promise(resolve => setTimeout(resolve, instance(_this).interval));
      const response = yield authenticatedPost.call(instance(_this).client, 'token', {
        form: true,
        body: { ...instance(_this).exchangeBody,
          grant_type: 'urn:ietf:params:oauth:grant-type:device_code',
          device_code: _this.device_code
        },
        json: true
      }, {
        clientAssertionPayload: instance(_this).clientAssertionPayload
      });
      let responseBody;

      try {
        responseBody = processResponse(response);
      } catch (err) {
        switch (err instanceof OPError && err.error) {
          case 'slow_down':
            instance(_this).interval += 5000;

          case 'authorization_pending':
            // eslint-disable-line no-fallthrough
            return _this.poll();

          default:
            throw err;
        }
      }

      const tokenset = new TokenSet(responseBody);

      if ('id_token' in tokenset) {
        yield instance(_this).client.decryptIdToken(tokenset);
        yield instance(_this).client.validateIdToken(tokenset, undefined, 'token', instance(_this).maxAge);
      }

      return tokenset;
    })();
  }

  get device_code() {
    return instance(this).response.device_code;
  }

  get user_code() {
    return instance(this).response.user_code;
  }

  get verification_uri() {
    return instance(this).response.verification_uri;
  }

  get verification_uri_complete() {
    return instance(this).response.verification_uri_complete;
  }

  get expires_in() {
    return Math.max.apply(null, [instance(this).expires_at - now(), 0]);
  }

  expired() {
    return this.expires_in === 0;
  }
  /* istanbul ignore next */


  [inspect.custom]() {
    return `${this.constructor.name} ${inspect(instance(this).response, {
      depth: Infinity,
      colors: process.stdout.isTTY,
      compact: false,
      sorted: true
    })}`;
  }

}

module.exports = DeviceFlowHandle;