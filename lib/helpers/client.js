"use strict";

function asyncGeneratorStep(gen, resolve, reject, _next, _throw, key, arg) { try { var info = gen[key](arg); var value = info.value; } catch (error) { reject(error); return; } if (info.done) { resolve(value); } else { Promise.resolve(value).then(_next, _throw); } }

function _asyncToGenerator(fn) { return function () { var self = this, args = arguments; return new Promise(function (resolve, reject) { var gen = fn.apply(self, args); function _next(value) { asyncGeneratorStep(gen, resolve, reject, _next, _throw, "next", value); } function _throw(err) { asyncGeneratorStep(gen, resolve, reject, _next, _throw, "throw", err); } _next(undefined); }); }; }

const jose = require('jose');

const {
  assertIssuerConfiguration
} = require('./assert');

const {
  random
} = require('./generators');

const now = require('./unix_timestamp');

const request = require('./request');

const instance = require('./weak_cache');

const merge = require('./merge');

const formUrlEncode = value => encodeURIComponent(value).replace(/%20/g, '+');

function clientAssertion(_x, _x2) {
  return _clientAssertion.apply(this, arguments);
}

function _clientAssertion() {
  _clientAssertion = _asyncToGenerator(function* (endpoint, payload) {
    let alg = this[`${endpoint}_endpoint_auth_signing_alg`];

    if (!alg) {
      assertIssuerConfiguration(this.issuer, `${endpoint}_endpoint_auth_signing_alg_values_supported`);
    }

    if (this[`${endpoint}_endpoint_auth_method`] === 'client_secret_jwt') {
      const key = yield this.joseSecret();

      if (!alg) {
        const supported = this.issuer[`${endpoint}_endpoint_auth_signing_alg_values_supported`];
        alg = Array.isArray(supported) && supported.find(signAlg => key.algorithms('sign').has(signAlg));
      }

      return jose.JWS.sign(payload, key, {
        alg,
        typ: 'JWT'
      });
    }

    const keystore = instance(this).get('keystore');

    if (!keystore) {
      throw new TypeError('no client jwks provided for signing a client assertion with');
    }

    if (!alg) {
      const algs = new Set();
      keystore.all().forEach(key => {
        key.algorithms('sign').forEach(Set.prototype.add.bind(algs));
      });
      const supported = this.issuer[`${endpoint}_endpoint_auth_signing_alg_values_supported`];
      alg = Array.isArray(supported) && supported.find(signAlg => algs.has(signAlg));
    }

    const key = keystore.get({
      alg,
      use: 'sig'
    });

    if (!key) {
      throw new TypeError(`no key found in client jwks to sign a client assertion with using alg ${alg}`);
    }

    return jose.JWS.sign(payload, key, {
      alg,
      typ: 'JWT',
      kid: key.kid
    });
  });
  return _clientAssertion.apply(this, arguments);
}

function authFor(_x3) {
  return _authFor.apply(this, arguments);
}

function _authFor() {
  _authFor = _asyncToGenerator(function* (endpoint, {
    clientAssertionPayload
  } = {}) {
    const authMethod = this[`${endpoint}_endpoint_auth_method`];

    switch (authMethod) {
      case 'self_signed_tls_client_auth':
      case 'tls_client_auth':
      case 'none':
        return {
          body: {
            client_id: this.client_id
          }
        };

      case 'client_secret_post':
        if (!this.client_secret) {
          throw new TypeError('client_secret_post client authentication method requires a client_secret');
        }

        return {
          body: {
            client_id: this.client_id,
            client_secret: this.client_secret
          }
        };

      case 'private_key_jwt':
      case 'client_secret_jwt':
        {
          const timestamp = now();
          const assertion = yield clientAssertion.call(this, endpoint, {
            iat: timestamp,
            exp: timestamp + 60,
            jti: random(),
            iss: this.client_id,
            sub: this.client_id,
            aud: this.issuer[`${endpoint}_endpoint`],
            // TODO: in v4.x pass the issuer instead (for now clientAssertionPayload can be used for that)
            ...clientAssertionPayload
          });
          return {
            body: {
              client_id: this.client_id,
              client_assertion: assertion,
              client_assertion_type: 'urn:ietf:params:oauth:client-assertion-type:jwt-bearer'
            }
          };
        }

      default:
        {
          // client_secret_basic
          // This is correct behaviour, see https://tools.ietf.org/html/rfc6749#section-2.3.1 and the
          // related appendix. (also https://github.com/panva/node-openid-client/pull/91)
          // > The client identifier is encoded using the
          // > "application/x-www-form-urlencoded" encoding algorithm per
          // > Appendix B, and the encoded value is used as the username; the client
          // > password is encoded using the same algorithm and used as the
          // > password.
          if (!this.client_secret) {
            throw new TypeError('client_secret_basic client authentication method requires a client_secret');
          }

          const encoded = `${formUrlEncode(this.client_id)}:${formUrlEncode(this.client_secret)}`;
          const value = Buffer.from(encoded).toString('base64');
          return {
            headers: {
              Authorization: `Basic ${value}`
            }
          };
        }
    }
  });
  return _authFor.apply(this, arguments);
}

function resolveResponseType() {
  const {
    length,
    0: value
  } = this.response_types;

  if (length === 1) {
    return value;
  }

  return undefined;
}

function resolveRedirectUri() {
  const {
    length,
    0: value
  } = this.redirect_uris || [];

  if (length === 1) {
    return value;
  }

  return undefined;
}

function authenticatedPost(_x4, _x5) {
  return _authenticatedPost.apply(this, arguments);
}

function _authenticatedPost() {
  _authenticatedPost = _asyncToGenerator(function* (endpoint, opts, {
    clientAssertionPayload,
    endpointAuthMethod = endpoint
  } = {}) {
    const auth = yield authFor.call(this, endpointAuthMethod, {
      clientAssertionPayload
    });
    const requestOpts = merge(opts, auth, {
      form: true
    });
    const mTLS = this[`${endpointAuthMethod}_endpoint_auth_method`].includes('tls_client_auth') || endpoint === 'token' && this.tls_client_certificate_bound_access_tokens;
    let targetUrl;

    if (mTLS && this.issuer.mtls_endpoint_aliases) {
      targetUrl = this.issuer.mtls_endpoint_aliases[`${endpoint}_endpoint`];
    }

    targetUrl = targetUrl || this.issuer[`${endpoint}_endpoint`];

    if ('body' in requestOpts) {
      for (const [key, value] of Object.entries(requestOpts.body)) {
        // eslint-disable-line no-restricted-syntax, max-len
        if (typeof value === 'undefined') {
          delete requestOpts.body[key];
        }
      }
    }

    return request.call(this, { ...requestOpts,
      method: 'POST',
      url: targetUrl
    }, {
      mTLS
    });
  });
  return _authenticatedPost.apply(this, arguments);
}

module.exports = {
  resolveResponseType,
  resolveRedirectUri,
  authFor,
  authenticatedPost
};